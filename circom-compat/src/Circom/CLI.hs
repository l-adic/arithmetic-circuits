module Circom.CLI (defaultMain) where

import Circom.R1CS (R1CSHeader (rhPrime), decodeR1CSHeaderFromFile, r1csFromCircomR1CS, r1csToCircomR1CS, witnessFromCircomWitness)
import Circom.Solver (CircomProgram (..), mkCircomProgram, nativeGenWitness)
import Circuit.Arithmetic (CircuitVars (..), InputBindings (labelToVar), restrictVars)
import Circuit.Dataflow qualified as DataFlow
import Circuit.Dot (arithCircuitToDot)
import Circuit.Language.Compile (BuilderState (..), ExprM, runCircuitBuilder)
import Data.Aeson (decodeFileStrict)
import Data.Aeson qualified as A
import Data.Binary (decodeFile, encodeFile)
import Data.Field.Galois (Prime, PrimeField (fromP))
import Data.IntSet qualified as IntSet
import Data.Text qualified as Text
import GHC.TypeNats (SNat, withKnownNat, withSomeSNat)
import Options.Applicative (CommandFields, Mod, Parser, ParserInfo, command, execParser, fullDesc, header, help, helper, hsubparser, info, long, progDesc, showDefault, strOption, switch, value)
import Protolude
import R1CS (R1CS, Witness, isValidWitness, toR1CS)
import Data.Text.Read (decimal, hexadecimal)
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
    coCircuitBinFile :: FilePath
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
    soWitnessFile :: FilePath
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

data VerifyOpts = VerifyOpts
  { voR1CSFile :: FilePath
  , voWitnessFile :: FilePath
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
        let vars = cpVars prog
            inputsOnly = cvInputsLabels $ restrictVars vars (cvPrivateInputs vars `IntSet.union` cvPublicInputs vars)
            inputsTemplate = map (const A.Null) $ labelToVar inputsOnly
            inputsTemplateFilePath = Text.unpack progName <> "-inputs-template.json"
        A.encodeFile inputsTemplateFilePath inputsTemplate
      when (coIncludeJson compilerOpts) $ do
        A.encodeFile (r1csFilePath <> ".json") (map fromP r1cs)
        A.encodeFile (binFilePath <> ".json") (map fromP prog)
      when (coGenDotFile compilerOpts) $ do
        let dotFilePath = Text.unpack progName <> ".dot"
        writeFile dotFilePath $ arithCircuitToDot (cpCircuit prog)
    Solve solveOpts -> do
      inputs <- do
        mInputs <- decodeFileStrict (soInputsFile solveOpts)
        maybe (panic "Failed to decode inputs") (pure . map (fromInteger @f . unFieldElem)) mInputs
      let binFilePath = soCircuitBinFile solveOpts
      circuit <- decodeFile binFilePath 
      let wtns = nativeGenWitness circuit inputs
          wtnsFilePath =  soWitnessFile solveOpts
      encodeFile wtnsFilePath wtns
      when (soIncludeJson solveOpts) $ do
        A.encodeFile (wtnsFilePath <> ".json") (map fromP wtns)
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

newtype FieldElem = FieldElem {unFieldElem :: Integer} deriving newtype (Eq, Ord, Enum, Num, Real, Integral)

instance A.FromJSON FieldElem where
  parseJSON v = case v of
    A.String s ->
      case hexadecimal s <> decimal s of
        Left e -> fail e
        Right (a, rest) ->
          if Text.null rest
            then pure a
            else fail $ "FieldElem parser failed to consume all input: " <> Text.unpack rest
    _ -> FieldElem <$> A.parseJSON v