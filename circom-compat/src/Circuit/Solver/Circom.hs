module Circuit.Solver.Circom
  ( ProgramEnv (..),
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
    _setInputSignal,
    _getWitnessSize,
    _getWitness,
  )
where

import Circuit
import Data.Field.Galois (GaloisField, PrimeField (fromP), char)
import Data.IORef (IORef, readIORef, writeIORef)
import Data.Map qualified as Map
import Data.Propagator (PropagatedNum)
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.Mutable (IOVector)
import Data.Vector.Mutable qualified as MV
import FNV (FNVHash (..), hashText, mkFNV)
import Protolude
import R1CS (Inputs (..), Witness (..), oneVar)
import R1CS.Circom (FieldSize (..), integerFromLittleEndian, integerToLittleEndian, n32)

data ProgramEnv f = ProgramEnv
  { peFieldSize :: FieldSize,
    peRawPrime :: Integer,
    peVersion :: Int,
    peInputsSize :: Int,
    peWitnessSize :: Int,
    peCircuit :: ArithCircuit f,
    peCircuitVars :: CircuitVars FNVHash
  }

mkProgramEnv ::
  forall f.
  (GaloisField f) =>
  CircuitVars Text ->
  ArithCircuit f ->
  ProgramEnv f
mkProgramEnv vars circ =
  ProgramEnv
    { peFieldSize = FieldSize 32,
      peRawPrime = toInteger $ char (1 :: f),
      peVersion = 2,
      peInputsSize = Set.size $ cvPrivateInputs vars <> cvPublicInputs vars,
      peWitnessSize = Set.size $ Set.insert oneVar $ cvVars vars,
      peCircuit = circ,
      peCircuitVars = relabel hashText vars
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

-- | The arg is a bool representing 'sanityCheck'. We don't
-- need this at the moment
_init :: Int -> IO ()
_init = mempty

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

-- we ignore the last arugment because our signals don't have indices, only names
_setInputSignal ::
  forall f.
  (PrimeField f) =>
  (PropagatedNum f) =>
  ProgramEnv f ->
  IORef (ProgramState f) ->
  Word32 ->
  Word32 ->
  Int ->
  IO ()
_setInputSignal env@(ProgramEnv {peCircuit, peInputsSize, peCircuitVars}) stRef msb lsb _ = do
  st <- readIORef stRef
  let Inputs inputs = psInputs st
  let h = mkFNV msb lsb
      i = fromMaybe (panic $ "Hash not found: " <> show h) $ Map.lookup h (cvInputsLabels peCircuitVars)
  newInput <- fromInteger <$> readBuffer env stRef
  let newInputs = Map.insert i newInput inputs
  writeIORef stRef $
    if Map.size newInputs == peInputsSize
      then
        let wtns = solve newInputs peCircuitVars peCircuit
         in st
              { psInputs = Inputs newInputs,
                psWitness = Witness $ Map.insert oneVar 1 wtns
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
  let wtn = maybe (panic $ "missing witness " <> show i) fromP $ Map.lookup i wtns
   in writeBuffer env stRef wtn

--------------------------------------------------------------------------------

writeBuffer :: ProgramEnv f -> IORef (ProgramState f) -> Integer -> IO ()
writeBuffer (ProgramEnv {peFieldSize}) stRef x = do
  let chunks = integerToLittleEndian peFieldSize x
  forM_ [0 .. n32 peFieldSize - 1] $ \j ->
    _writeSharedRWMemory stRef j (chunks V.! j)

readBuffer :: ProgramEnv f -> IORef (ProgramState f) -> IO Integer
readBuffer (ProgramEnv {peFieldSize}) stRef = do
  v <- V.generateM (n32 peFieldSize) $ \j ->
    _readSharedRWMemory stRef j
  pure $ integerFromLittleEndian v
