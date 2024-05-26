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
import System.Directory (createDirectoryIfMissing)

data GlobalOpts = GlobalOpts
  { outputDir :: FilePath,
    cmd :: Command
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
        <$> strOption
          ( long "output-dir"
              <> help "output directory"
              <> showDefault
              <> value "circuit-output"
          )
        <*> hsubparser (compileCommand <> solveCommand <> verifyCommand)

    compileCommand :: Mod CommandFields Command
    compileCommand =
      command "compile" (info (Compile <$> compileOptsParser) (progDesc "Compile the program to an r1cs and constraint system"))

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
    coIncludeJson :: Bool
  }

compileOptsParser :: Parser CompileOpts
compileOptsParser =
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
      ( long "witness"
          <> help "witness output file"
          <> showDefault
          <> value (Text.unpack progName <> ".wtns")
      )

data VerifyOpts = VerifyOpts
  { voWitnessFile :: FilePath
  }

verifyOptsParser :: Text -> Parser VerifyOpts
verifyOptsParser progName =
  VerifyOpts
    <$> strOption
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
  let outDir = outputDir opts
  case cmd opts of
    Compile compilerOpts -> do
      let BuilderState {..} = snd $ runCircuitBuilder program
          prog = optimize (coOptimizeOpts compilerOpts) $ mkCircomProgram bsVars bsCircuit
          r1cs = r1csToCircomR1CS $ toR1CS (cpVars prog) (cpCircuit prog)
      createDirectoryIfMissing True outDir
      encodeFile (r1csFilePath outDir) r1cs
      encodeFile (binFilePath outDir) prog
      when (coGenInputsTemplate compilerOpts) $ do
        let vars = cpVars prog
            inputsOnly = cvInputsLabels $ restrictVars vars (cvPrivateInputs vars `IntSet.union` cvPublicInputs vars)
            inputsTemplate = map (const A.Null) $ labelToVar inputsOnly
        A.encodeFile (inputsTemplateFilePath outDir) inputsTemplate
      when (coIncludeJson compilerOpts) $ do
        A.encodeFile (r1csFilePath outDir <> ".json") (map fromP r1cs)
        A.encodeFile (binFilePath outDir <> ".json") (map fromP prog)
      when (coGenDotFile compilerOpts) $ do
        writeFile (dotFilePath outDir) $ arithCircuitToDot (cpCircuit prog)
    Solve solveOpts -> do
      inputs <- do
        mInputs <- decodeFileStrict (soInputsFile solveOpts)
        maybe (panic "Failed to decode inputs") (pure . map (fromInteger @f)) mInputs
      circuit <- decodeFile (binFilePath outDir)
      let wtns = nativeGenWitness circuit inputs
          wtnsFilePath = outDir <> "/" <> soWitnessFile solveOpts
      encodeFile wtnsFilePath wtns
      when (soIncludeJson solveOpts) $ do
        A.encodeFile (wtnsFilePath <> ".json") (map fromP wtns)
    Verify verifyOpts -> do
      cr1cs <- decodeR1CSHeaderFromFile (r1csFilePath outDir)
      withSomeSNat (fromInteger $ rhPrime cr1cs) $ \(snat :: SNat p) ->
        withKnownNat @p snat $ do
          r1cs :: R1CS (Prime p) <- r1csFromCircomR1CS <$> decodeFile (r1csFilePath outDir)
          let wtnsFilePath = outDir <> "/" <> voWitnessFile verifyOpts
          wtns :: Witness (Prime p) <- witnessFromCircomWitness <$> decodeFile wtnsFilePath
          if isValidWitness wtns r1cs
            then print ("Witness is valid" :: Text)
            else do
              print ("Witness is invalid" :: Text)
              exitFailure
  where
    baseFilePath :: FilePath -> FilePath
    baseFilePath dir = dir <> "/" <> Text.unpack progName
    inputsTemplateFilePath dir = dir <> "/" <> "inputs-template.json"
    binFilePath dir = baseFilePath dir <> ".bin"
    r1csFilePath dir = baseFilePath dir <> ".r1cs"
    dotFilePath dir = baseFilePath dir <> ".dot"

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
