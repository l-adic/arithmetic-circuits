module Circom.Solver
  ( CircomProgram,
    cpVars,
    cpCircuit,
    mkCircomProgram,
    ProgramEnv (..),
    mkProgramEnv,
    ProgramState (..),
    mkProgramState,
    _init,
    _getNVars,
    _getVersion,
    _getRawPrime,
    _writeSharedRWMemory,
    _readSharedRWMemory,
    _getFieldNumLen32,
    _getInputSize,
    _getInputSignalSize,
    _setInputSignal,
    _getWitnessSize,
    _getWitness,
    nativeGenWitness,
  )
where

import Circom.R1CS (CircomWitness, FieldSize (..), circomReindexMap, integerFromLittleEndian, integerToLittleEndian, n32, witnessToCircomWitness)
import Circuit
import Data.Aeson (ToJSON)
import Data.Binary (Binary)
import Data.Field.Galois (GaloisField, PrimeField (fromP), char)
import Data.IORef (IORef, modifyIORef', readIORef, writeIORef)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Vector qualified as V
import Data.Vector.Mutable (IOVector)
import Data.Vector.Mutable qualified as MV
import FNV (FNVHash (..), hashText, mkFNV)
import Protolude
import R1CS (Inputs (..), Witness (..), oneVar)
import Text.PrettyPrint.Leijen.Text (Pretty (pretty), (<+>))

data CircomProgram f = CircomProgram
  { cpVars :: CircuitVars Text,
    cpCircuit :: ArithCircuit f
  }
  deriving (Generic)

instance (Binary f) => Binary (CircomProgram f)

instance Functor CircomProgram where
  fmap f CircomProgram {cpVars, cpCircuit} =
    CircomProgram
      { cpVars,
        cpCircuit = fmap f cpCircuit
      }

instance (ToJSON f) => ToJSON (CircomProgram f)

mkCircomProgram ::
  CircuitVars Text ->
  ArithCircuit f ->
  CircomProgram f
mkCircomProgram vars circ =
  let f = circomReindexMap vars
   in CircomProgram
        { cpVars = reindex f vars,
          cpCircuit = reindex f circ
        }

-- WASM Solver

data ProgramEnv f = ProgramEnv
  { peFieldSize :: FieldSize,
    peRawPrime :: Integer,
    peVersion :: Int,
    peInputsSize :: Int,
    peWitnessSize :: Int,
    peCircuit :: ArithCircuit f,
    peSignalSizes :: Map FNVHash Int,
    peCircuitVars :: CircuitVars FNVHash
  }

mkProgramEnv ::
  forall f.
  (GaloisField f) =>
  CircomProgram f ->
  ProgramEnv f
mkProgramEnv CircomProgram {cpVars = vars, cpCircuit = circ} =
  let vs = relabel hashText vars
  in ProgramEnv
    { peFieldSize = FieldSize 32,
      peRawPrime = toInteger $ char (1 :: f),
      peVersion = 2,
      peInputsSize = IntSet.size $ cvPrivateInputs vars <> cvPublicInputs vars,
      peWitnessSize = IntSet.size $ IntSet.insert oneVar $ cvVars vars,
      peCircuit = circ,
      peSignalSizes = inputSizes (cvInputsLabels vs),
      peCircuitVars = vs
    }

data ProgramState f = ProgramState
  { psInputs :: Inputs f,
    psWitness :: Witness f,
    psSharedRWMemory :: IOVector Word32
  }

mkProgramState ::
  ProgramEnv f ->
  IO (ProgramState f)
mkProgramState ProgramEnv {peFieldSize} = do
  sharedRWMemory <- MV.replicate (n32 peFieldSize) 0
  pure
    ProgramState
      { psInputs = Inputs mempty,
        psWitness = Witness mempty,
        psSharedRWMemory = sharedRWMemory
      }

_init :: ProgramEnv f -> IORef (ProgramState f) -> Int -> IO ()
_init env stRef _ = do
  writeBuffer env stRef 0
  modifyIORef' stRef $ \st ->
    st
      { psInputs = Inputs mempty,
        psWitness = Witness mempty
      }

_getNVars :: ProgramEnv f -> Int
_getNVars = peWitnessSize

_getVersion :: ProgramEnv f -> Int
_getVersion = peVersion

_getRawPrime :: ProgramEnv f -> IORef (ProgramState f) -> IO ()
_getRawPrime env@ProgramEnv {peRawPrime} stRef =
  writeBuffer env stRef peRawPrime

_writeSharedRWMemory :: IORef (ProgramState f) -> Int -> Word32 -> IO ()
_writeSharedRWMemory stRef i v =
  readIORef stRef >>= \st ->
    MV.write (psSharedRWMemory st) i v

_readSharedRWMemory :: IORef (ProgramState f) -> Int -> IO Word32
_readSharedRWMemory stRef i =
  readIORef stRef >>= \st ->
    MV.read (psSharedRWMemory st) i

_getFieldNumLen32 :: ProgramEnv f -> Int
_getFieldNumLen32 ProgramEnv {peFieldSize} = n32 peFieldSize

_getInputSize :: ProgramEnv f -> Int
_getInputSize = peInputsSize

-- we dont (yet) support multiple values (e.g. arrays) for signal values
_getInputSignalSize :: ProgramEnv f -> Word32 -> Word32 -> IO Int
_getInputSignalSize ProgramEnv {peSignalSizes} msb lsb = 
  let h = mkFNV msb lsb
  in pure $ fromMaybe 0 $ Map.lookup h peSignalSizes
  

-- we ignore the last arugment because our signals don't have indices, only names
_setInputSignal ::
  forall f.
  (PrimeField f) =>
  ProgramEnv f ->
  IORef (ProgramState f) ->
  Word32 ->
  Word32 ->
  Int ->
  IO ()
_setInputSignal env@(ProgramEnv {peCircuit, peInputsSize, peCircuitVars}) stRef msb lsb i = do
  st <- readIORef stRef
  let Inputs inputs = psInputs st
  let h = mkFNV msb lsb
      v = fromMaybe (panic $ "Hash not found: " <> show h) $ Map.lookup (h, i) (labelToVar $ cvInputsLabels peCircuitVars)
  newInput <- fromInteger <$> readBuffer env stRef
  let newInputs = IntMap.insert v newInput inputs
  writeIORef stRef $
    if IntMap.size newInputs == peInputsSize
      then
        let wtns =
              evalArithCircuit
                (\w a -> IntMap.lookup (wireName w) a)
                (\w a -> safeAssign (wireName w) a)
                peCircuit
                newInputs
         in st
              { psInputs = Inputs newInputs,
                psWitness = Witness $ IntMap.insert oneVar 1 wtns
              }
      else st {psInputs = Inputs newInputs}

_getWitnessSize :: ProgramEnv f -> Int
_getWitnessSize = peWitnessSize

_getWitness ::
  (PrimeField f) =>
  ProgramEnv f ->
  IORef (ProgramState f) ->
  Int ->
  IO ()
_getWitness env stRef i = do
  ProgramState {psWitness = Witness wtns} <- readIORef stRef
  let wtn = maybe (panic $ "missing witness " <> show i) fromP $ IntMap.lookup i wtns
   in writeBuffer env stRef wtn

--------------------------------------------------------------------------------
-- Standard Solver (to be used as native executable)

nativeGenWitness ::
  forall f.
  (PrimeField f) =>
  CircomProgram f ->
  Map Text (VarType f) ->
  CircomWitness f
nativeGenWitness CircomProgram {cpVars = vars, cpCircuit = circ} inputs =
  let initAssignments = assignInputs vars inputs
      wtns =
        evalArithCircuit
          (\w a -> IntMap.lookup (wireName w) a)
          (\w a -> safeAssign (wireName w) a)
          circ
          initAssignments
   in witnessToCircomWitness $ Witness wtns

--------------------------------------------------------------------------------

{-# INLINE safeAssign #-}
safeAssign :: (Eq f) => (Pretty f) => Int -> f -> IntMap f -> IntMap f
safeAssign =
  let f k new old =
        if new == old
          then new
          else panic $ show $ "Assignment contradiction for var" <+> pretty k <> ":" <> pretty new <+> " /= " <+> pretty old
   in IntMap.insertWithKey f

{-# INLINE writeBuffer #-}
writeBuffer :: ProgramEnv f -> IORef (ProgramState f) -> Integer -> IO ()
writeBuffer (ProgramEnv {peFieldSize}) stRef x = do
  let chunks = integerToLittleEndian peFieldSize x
  forM_ [0 .. n32 peFieldSize - 1] $ \j ->
    _writeSharedRWMemory stRef j (chunks V.! j)

{-# INLINE readBuffer #-}
readBuffer :: ProgramEnv f -> IORef (ProgramState f) -> IO Integer
readBuffer (ProgramEnv {peFieldSize}) stRef = do
  v <- V.generateM (n32 peFieldSize) $ \j ->
    _readSharedRWMemory stRef j
  pure $ integerFromLittleEndian v
