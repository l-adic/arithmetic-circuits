{-# LANGUAGE TemplateHaskellQuotes #-}

module Circuit.Solver.Circom (mkProgram) where

import Circuit
import Data.Field.Galois (GaloisField, PrimeField (fromP), char)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Map qualified as Map
import Data.Propagator (PropagatedNum)
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.Mutable (IOVector)
import Data.Vector.Mutable qualified as MV
import FNV (FNVHash (..), hashText, mkFNV)
import Language.Haskell.TH
import Protolude
import R1CS (Inputs (..), Witness (..), oneVar)
import R1CS.Circom (FieldSize (..), integerFromLittleEndian, integerToLittleEndian, n32)
import System.IO.Unsafe (unsafePerformIO)

data ProgramEnv f = ProgramEnv
  { peFieldSize :: FieldSize,
    peRawPrime :: Integer,
    peVersion :: Int,
    peSharedRWMemory :: IOVector Word32,
    peCircuit :: ArithCircuit f
  }

mkProgramEnv ::
  forall f.
  (GaloisField f) =>
  ArithCircuit f ->
  IO (ProgramEnv f)
mkProgramEnv circ = do
  let fieldSize = FieldSize 32
  sharedRWMemory <- MV.replicate (n32 fieldSize) 0
  pure
    ProgramEnv
      { peFieldSize = FieldSize 32,
        peRawPrime = toInteger $ char (1 :: f),
        peVersion = 2,
        peSharedRWMemory = sharedRWMemory,
        peCircuit = circ
      }

data ProgramState f = ProgramState
  { psInputsSize :: Int,
    psInputs :: Inputs f,
    psWitnessSize :: Int,
    psWitness :: Witness f,
    psInputsLabels :: Map FNVHash Int
  }

mkProgramState ::
  CircuitVars Text ->
  ProgramState f
mkProgramState vs =
  ProgramState
    { psInputsSize = Set.size $ cvPrivateInputs vs <> cvPublicInputs vs,
      psInputs = Inputs mempty,
      psWitnessSize = Set.size $ Set.insert oneVar $ cvVars vs,
      psWitness = Witness mempty,
      psInputsLabels = cvInputsLabels $ relabel hashText vs
    }

-- | The arg is a bool representing 'sanityCheck'. We don't
-- need this at the moment
_init :: Int -> IO ()
_init = mempty

_getNVars :: IORef (ProgramState f) -> IO Int
_getNVars st = readIORef st <&> psWitnessSize

_getVersion :: ProgramEnv f -> Int
_getVersion = peVersion

_getRawPrime :: ProgramEnv f -> IO ()
_getRawPrime env@ProgramEnv {peRawPrime} =
  writeBuffer env peRawPrime

_writeSharedRWMemory :: ProgramEnv f -> Int -> Word32 -> IO ()
_writeSharedRWMemory env i v = MV.write (peSharedRWMemory env) i v

_readSharedRWMemory :: ProgramEnv f -> Int -> IO Word32
_readSharedRWMemory env i = MV.read (peSharedRWMemory env) i

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
_setInputSignal env@(ProgramEnv {peCircuit}) stRef msb lsb _ = do
  st <- readIORef stRef
  let Inputs inputs = psInputs st
  let h = mkFNV msb lsb
      i = fromMaybe (panic $ "Hash not found: " <> show h) $ Map.lookup h (psInputsLabels st)
  newInput <- fromInteger <$> readBuffer env
  let newInputs = Map.insert i newInput inputs
  writeIORef stRef $
    if Map.size newInputs == psInputsSize st
      then
        let wtns = solve newInputs peCircuit
         in st
              { psInputs = Inputs newInputs,
                psWitness = Witness $ Map.insert oneVar 1 wtns
              }
      else st {psInputs = Inputs newInputs}

_getWitnessSize :: IORef (ProgramState f) -> IO Int
_getWitnessSize st = readIORef st <&> psWitnessSize

_getWitness ::
  (PrimeField f) =>
  ProgramEnv f ->
  IORef (ProgramState f) ->
  Int ->
  IO ()
_getWitness env st i = do
  ProgramState {psWitness = Witness wtns} <- readIORef st
  let wtn = maybe (panic $ "missing witness " <> show i) fromP $ Map.lookup i wtns
   in writeBuffer env wtn

writeBuffer :: ProgramEnv f -> Integer -> IO ()
writeBuffer env@(ProgramEnv {peFieldSize}) x = do
  let chunks = integerToLittleEndian peFieldSize x
  forM_ [0 .. n32 peFieldSize - 1] $ \j ->
    _writeSharedRWMemory env j (chunks V.! j)

readBuffer :: ProgramEnv f -> IO Integer
readBuffer env@(ProgramEnv {peFieldSize}) = do
  v <- V.generateM (n32 peFieldSize) $ \j ->
    _readSharedRWMemory env j
  pure $ integerFromLittleEndian v

mkProgram :: Name -> Name -> Name -> DecsQ
mkProgram env s f = do
  let stateName = mkName "programStateRef"
  let envName = mkName "programEnv"
  let mkForeignExport fName ty =
        ty >>= \_t -> return (ForeignD $ ExportF CCall "" fName _t)
  let stateRefDecls =
        let ty =
              (conT ''IORef) `appT` (conT ''ProgramState `appT` conT f)
            body =
              (varE 'unsafePerformIO) `appE` (varE 'newIORef `appE` (varE 'mkProgramState `appE` varE s))
         in [ sigD stateName ty,
              valD (varP stateName) (normalB body) []
            ]
      envDecls =
        let ty = conT ''ProgramEnv `appT` conT f
            body = varE 'unsafePerformIO `appE` (varE 'mkProgramEnv `appE` varE env)
         in [ sigD envName ty,
              valD (varP envName) (normalB body) []
            ]
      initDecls =
        let fName = mkName "init"
            ty = appT arrowT (conT ''Int) `appT` (conT ''IO `appT` conT ''())
         in [ sigD fName ty,
              valD (varP fName) (normalB [|mempty|]) [],
              mkForeignExport fName ty
            ]

      getNVarsDecls =
        let fName = mkName "getNVars"
            ty = conT ''IO `appT` conT ''Int
            body = varE '_getNVars `appE` varE stateName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      getVersionDecls =
        let fName = mkName "getVersion"
            ty = conT ''Int
            body = varE '_getVersion `appE` varE envName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      getRawPrimeDecls =
        let fName = mkName "getRawPrime"
            ty = conT ''IO `appT` conT ''()
            body = varE '_getRawPrime `appE` varE envName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      writeSharedRWMemoryDecls = do
        let fName = mkName "writeSharedRWMemory"
            ty =
              appT arrowT (conT ''Int)
                `appT` (appT arrowT (conT ''Word32) `appT` (conT ''IO `appT` conT ''()))
            body = varE '_writeSharedRWMemory `appE` varE envName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      readSharedRWMemoryDecls =
        let fName = mkName "readSharedRWMemory"
            ty = appT arrowT (conT ''Int) `appT` (conT ''IO `appT` conT ''Word32)
            body = varE '_readSharedRWMemory `appE` varE envName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      getFieldNumLen32Decls =
        let fName = mkName "getFieldNumLen32"
            ty = conT ''Int
            body = varE '_getFieldNumLen32 `appE` varE envName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      setInputSignalDecls =
        let fName = mkName "setInputSignal"
            ty =
              appT arrowT (conT ''Word32)
                `appT` (appT arrowT (conT ''Word32) `appT` (appT arrowT (conT ''Int) `appT` (conT ''IO `appT` conT ''())))
            body = varE '_setInputSignal `appE` varE envName `appE` varE stateName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      getWitnessSizeDecls =
        let fName = mkName "getWitnessSize"
            ty = conT ''IO `appT` conT ''Int
            body = varE '_getWitnessSize `appE` varE stateName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

      getWitnessDecls =
        let fName = mkName "getWitness"
            ty = appT arrowT (conT ''Int) `appT` (conT ''IO `appT` conT ''())
            body = varE '_getWitness `appE` varE envName `appE` varE stateName
         in [ sigD fName ty,
              valD (varP fName) (normalB body) [],
              mkForeignExport fName ty
            ]

  sequence . concat $
    [ stateRefDecls,
      envDecls,
      initDecls,
      getNVarsDecls,
      getVersionDecls,
      getRawPrimeDecls,
      writeSharedRWMemoryDecls,
      readSharedRWMemoryDecls,
      getFieldNumLen32Decls,
      setInputSignalDecls,
      getWitnessSizeDecls,
      getWitnessDecls
    ]
