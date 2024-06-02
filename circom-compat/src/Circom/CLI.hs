module Circom.CLI (defaultMain) where

import Circom.R1CS (R1CSHeader (rhPrime), decodeR1CSHeaderFromFile, r1csFromCircomR1CS, r1csToCircomR1CS, witnessFromCircomWitness)
import Circom.Solver (CircomProgram (..), mkCircomProgram, nativeGenWitness)
import Circuit.Arithmetic (CircuitVars (..), InputBindings (labelToVar), VarType (..), inputSizes, restrictVars)
import Circuit.Dataflow qualified as DataFlow
import Circuit.Dot (arithCircuitToDot)
import Circuit.Language.Compile (BuilderState (..), ExprM, runCircuitBuilder)
import Control.Error (hoistEither)
import Data.Aeson qualified as A
import Data.Aeson.Types qualified as A
import Data.Binary (decodeFile, encodeFile)
import Data.Field.Galois (Prime, PrimeField (fromP))
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Data.Text qualified as Text
import Data.Text.Read (decimal, hexadecimal)
import GHC.TypeNats (SNat, withKnownNat, withSomeSNat)
import Numeric (showHex)
import Options.Applicative (CommandFields, Mod, Parser, ParserInfo, command, eitherReader, execParser, fullDesc, header, help, helper, hsubparser, info, long, option, progDesc, showDefault, showDefaultWith, strOption, switch, value)
import Protolude
import R1CS (R1CS, Witness (Witness), isValidWitness, toR1CS)
import Prelude (MonadFail (fail))

data GlobalOpts = GlobalOpts
  { cmd :: Command
  }

optsParser :: Text -> ParserInfo GlobalOpts
optsParser progName =
  info
    (helper <*> globalOptsParser)
    ( fullDesc
        <> progDesc ("Compiling " <> Text.unpack progName <> " to a zk-SNARK")
        <> header ("Compile " <> Text.unpack progName <> " to a system of constraints and solve for a witness")
    )
  where
    globalOptsParser :: Parser GlobalOpts
    globalOptsParser =
      GlobalOpts
        <$> hsubparser (compileCommand <> solveCommand <> verifyCommand)

    compileCommand :: Mod CommandFields Command
    compileCommand =
      command "compile" (info (Compile <$> compileOptsParser progName) (progDesc "Compile the program to an r1cs and constraint system"))

    solveCommand :: Mod CommandFields Command
    solveCommand =
      command "solve" (info (Solve <$> solveOptsParser progName) (progDesc "Generate a witness"))

    verifyCommand :: Mod CommandFields Command
    verifyCommand =
      command "verify" (info (Verify <$> verifyOptsParser progName) (progDesc "Verify a witness"))

data Command
  = Compile CompileOpts
  | Solve SolveOpts
  | Verify VerifyOpts

data CompileOpts = CompileOpts
  { coOptimizeOpts :: OptimizeOpts,
    coGenInputsTemplate :: Bool,
    coGenDotFile :: Bool,
    coIncludeJson :: Bool,
    coR1CSFile :: FilePath,
    coCircuitBinFile :: FilePath,
    coEncoding :: Encoding
  }

compileOptsParser :: Text -> Parser CompileOpts
compileOptsParser progName =
  CompileOpts
    <$> optimizeOptsParser
    <*> switch
      ( long "inputs-template"
          <> help "generate a template json file for the inputs"
      )
    <*> switch
      ( long "dot"
          <> help "generate a dot file for the circuit"
      )
    <*> switch
      ( long "json"
          <> help "also write json versions of artifacts"
      )
    <*> strOption
      ( long "r1cs"
          <> help "r1cs output file"
          <> showDefault
          <> value (Text.unpack progName <> ".r1cs")
      )
    <*> strOption
      ( long "constraints"
          <> help "constraints output bin file"
          <> showDefault
          <> value (Text.unpack progName <> ".bin")
      )
    <*> encodingParser

encodingParser :: Parser Encoding
encodingParser =
  let readEncoding = eitherReader $ \case
        "hex" -> pure HexString
        "decimal-string" -> pure DecString
        "decimal" -> pure Dec
        _ -> throwError $ "Invalid encoding, expected one of: hex, decimal-string, decimal"
   in option
        readEncoding
        ( long "encoding"
            <> help "encoding for inputs and outputs"
            <> showDefaultWith
              ( \case
                  HexString -> "hex"
                  DecString -> "decimal-string"
                  Dec -> "decimal"
              )
            <> value Dec
        )

data OptimizeOpts = OptimizeOpts
  { removeUnreachable :: Bool
  }

optimizeOptsParser :: Parser OptimizeOpts
optimizeOptsParser =
  OptimizeOpts
    <$> switch
      ( long "remove-unreachable"
          <> help "detect and remove variables not contributing to the output"
      )

data SolveOpts = SolveOpts
  { soInputsFile :: FilePath,
    soIncludeJson :: Bool,
    soCircuitBinFile :: FilePath,
    soWitnessFile :: FilePath,
    soShowOutputs :: Bool,
    soEncoding :: Encoding
  }

solveOptsParser :: Text -> Parser SolveOpts
solveOptsParser progName =
  SolveOpts
    <$> strOption
      ( long "inputs"
          <> help "inputs json file"
          <> showDefault
          <> value "inputs.json"
      )
    <*> switch
      ( long "json"
          <> help "also write json versions of artifacts"
      )
    <*> strOption
      ( long "constraints"
          <> help "constraints output bin file"
          <> showDefault
          <> value (Text.unpack progName <> ".bin")
      )
    <*> strOption
      ( long "witness"
          <> help "witness output file"
          <> showDefault
          <> value (Text.unpack progName <> ".wtns")
      )
    <*> switch
      ( long "show-outputs"
          <> help "print the output values as json"
      )
    <*> encodingParser

data VerifyOpts = VerifyOpts
  { voR1CSFile :: FilePath,
    voWitnessFile :: FilePath
  }

verifyOptsParser :: Text -> Parser VerifyOpts
verifyOptsParser progName =
  VerifyOpts
    <$> strOption
      ( long "r1cs"
          <> help "r1cs file"
          <> showDefault
          <> value (Text.unpack progName <> ".r1cs")
      )
    <*> strOption
      ( long "witness"
          <> help "witness file"
          <> showDefault
          <> value (Text.unpack progName <> ".wtns")
      )

defaultMain ::
  forall f a.
  (PrimeField f) =>
  Text ->
  ExprM f a ->
  IO ()
defaultMain progName program = do
  opts <- execParser (optsParser progName)
  case cmd opts of
    Compile compilerOpts -> do
      let BuilderState {..} = snd $ runCircuitBuilder program
          prog = optimize (coOptimizeOpts compilerOpts) $ mkCircomProgram bsVars bsCircuit
          r1cs = r1csToCircomR1CS $ toR1CS (cpVars prog) (cpCircuit prog)
      let r1csFilePath = coR1CSFile compilerOpts
      encodeFile r1csFilePath r1cs
      let binFilePath = coCircuitBinFile compilerOpts
      encodeFile binFilePath prog
      when (coGenInputsTemplate compilerOpts) $ do
        let inputsTemplate = mkInputsTemplate (coEncoding compilerOpts) (cpVars prog)
            inputsTemplateFilePath = Text.unpack progName <> "-inputs-template.json"
        writeIOVars inputsTemplateFilePath inputsTemplate
      when (coIncludeJson compilerOpts) $ do
        A.encodeFile (r1csFilePath <> ".json") (map fromP r1cs)
        A.encodeFile (binFilePath <> ".json") (map fromP prog)
      when (coGenDotFile compilerOpts) $ do
        let dotFilePath = Text.unpack progName <> ".dot"
        writeFile dotFilePath $ arithCircuitToDot (cpCircuit prog)
    Solve solveOpts -> do
      inputs <- do
        IOVars _ is <- readIOVars (soEncoding solveOpts) (soInputsFile solveOpts)
        pure $ map (map (fromInteger @f . unFieldElem)) is
      let binFilePath = soCircuitBinFile solveOpts
      circuit <- decodeFile binFilePath
      let wtns = nativeGenWitness circuit inputs
          wtnsFilePath = soWitnessFile solveOpts
      encodeFile wtnsFilePath wtns
      when (soIncludeJson solveOpts) $ do
        A.encodeFile (wtnsFilePath <> ".json") (map fromP wtns)
      when (soShowOutputs solveOpts) $ do
        let outputs = mkOutputs (soEncoding solveOpts) (cpVars circuit) (witnessFromCircomWitness wtns)
        print $ A.encode $ encodeIOVars outputs
    Verify verifyOpts -> do
      let r1csFilePath = voR1CSFile verifyOpts
      cr1cs <- decodeR1CSHeaderFromFile r1csFilePath
      withSomeSNat (fromInteger $ rhPrime cr1cs) $ \(snat :: SNat p) ->
        withKnownNat @p snat $ do
          r1cs :: R1CS (Prime p) <- r1csFromCircomR1CS <$> decodeFile r1csFilePath
          let wtnsFilePath = voWitnessFile verifyOpts
          wtns :: Witness (Prime p) <- witnessFromCircomWitness <$> decodeFile wtnsFilePath
          if isValidWitness wtns r1cs
            then print ("Witness is valid" :: Text)
            else do
              print ("Witness is invalid" :: Text)
              exitFailure

optimize ::
  forall f.
  (Ord f) =>
  OptimizeOpts ->
  CircomProgram f ->
  CircomProgram f
optimize opts =
  appEndo . mconcat $
    [ performRemoveUnreachable
    ]
  where
    performRemoveUnreachable :: Endo (CircomProgram f)
    performRemoveUnreachable =
      if (removeUnreachable opts)
        then Endo $ \prog ->
          let outVars :: [Int]
              outVars = IntSet.toList $ cvOutputs $ cpVars prog
              (newCircuit, usedVars) = DataFlow.removeUnreachable outVars (cpCircuit prog)
              newVars = restrictVars (cpVars prog) usedVars
           in mkCircomProgram newVars newCircuit
        else mempty

--------------------------------------------------------------------------------
-- Programs expecting to interact with Circom via the file system and solver API can
-- be all over the place w.r.t. to accepting / demanding inputs be encoded as strings (either hex or dec)
-- or as numbers.

data Encoding = HexString | DecString | Dec deriving (Eq, Show)

newtype FieldElem = FieldElem {unFieldElem :: Integer} deriving newtype (Eq, Ord, Enum, Num, Real, Integral)

encodeFieldElem :: Encoding -> FieldElem -> A.Value
encodeFieldElem enc (FieldElem a) = case enc of
  HexString -> A.toJSON $ "0x" <> (Text.pack $ showHex a "")
  DecString -> A.toJSON $ Text.pack $ show a
  Dec -> A.toJSON a

decodeFieldElem :: Encoding -> A.Value -> A.Parser FieldElem
decodeFieldElem enc _v = case enc of
  Dec -> FieldElem <$> A.parseJSON _v
  DecString -> do
    s <- A.parseJSON _v
    FieldElem <$> parseDec s
    where
      parseDec str = case decimal str of
        Right (n, "") -> pure n
        _ -> fail "FieldElem: expected a decimal string"
  HexString -> do
    s <- A.parseJSON _v
    FieldElem <$> parseHex s
    where
      parseHex str = case hexadecimal str of
        Right (n, "") -> pure n
        _ -> fail "FieldElem: expected a hexadecimal string"

encodeVarType :: Encoding -> VarType FieldElem -> A.Value
encodeVarType enc = \case
  Simple a -> encodeFieldElem enc a
  Array as -> A.toJSON $ map (encodeFieldElem enc) as

decodeVarType :: Encoding -> A.Value -> A.Parser (VarType FieldElem)
decodeVarType enc v = do
  vs <- A.parseJSON v
  case vs of
    A.Array as -> Array <$> traverse (decodeFieldElem enc) (toList as)
    _ -> Simple <$> decodeFieldElem enc v

data IOVars = IOVars Encoding (Map Text (VarType FieldElem))

encodeIOVars :: IOVars -> A.Value
encodeIOVars (IOVars enc vs) = A.toJSON $ map (encodeVarType enc) vs

decodeIOVars :: Encoding -> A.Value -> A.Parser IOVars
decodeIOVars enc v = do
  kvs <- A.parseJSON v
  IOVars enc <$> traverse (decodeVarType enc) kvs

mkInputsTemplate :: Encoding -> CircuitVars Text -> IOVars
mkInputsTemplate enc vars =
  let inputsOnly = cvInputsLabels $ restrictVars vars (cvPrivateInputs vars `IntSet.union` cvPublicInputs vars)
      vs = Map.toList $ inputSizes inputsOnly
      f (label, mlen) =
        case mlen of
          Nothing -> (label, Simple 0)
          Just len -> (label, Array (replicate len 0))
   in IOVars enc $ Map.fromList $ map f vs

mkOutputs :: (PrimeField f) => Encoding -> CircuitVars Text -> Witness f -> IOVars
mkOutputs enc vars (Witness w) =
  let vs :: [[((Text, Maybe Int), Int)]]
      vs =
        groupBy (\a b -> fst (fst a) == fst (fst b)) $
          Map.toList $
            Map.filter (\a -> a `IntSet.member` cvOutputs vars) $
              labelToVar $
                cvInputsLabels vars
      f = \case
        [((label, _), v)] ->
          let val = fromJust $ IntMap.lookup v w
           in (label, Simple . FieldElem . fromP $ val)
        as@(((l, _), _) : _) ->
          ( l,
            Array $ fromJust $ for as $ \(_, i) ->
              FieldElem . fromP <$> IntMap.lookup i w
          )
        _ -> panic "impossible: groupBy lists are non empty"
   in IOVars enc (Map.fromList $ map f vs)

writeIOVars :: FilePath -> IOVars -> IO ()
writeIOVars fp (IOVars enc vs) = A.encodeFile fp (encodeIOVars (IOVars enc vs))

readIOVars :: Encoding -> FilePath -> IO IOVars
readIOVars enc fp = map (either (panic . Text.pack) identity) $ runExceptT $ do
  contents <- ExceptT $ A.eitherDecodeFileStrict fp
  hoistEither $ A.parseEither (decodeIOVars enc) contents
