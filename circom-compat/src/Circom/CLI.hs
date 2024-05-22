module Circom.CLI (defaultMain) where

import Circom.R1CS (r1csToCircomR1CS)
import Circom.Solver (CircomProgram (..), mkCircomProgram, nativeGenWitness)
import Circuit.Arithmetic (CircuitVars (cvInputsLabels), InputBidings (labelToVar))
import Circuit.Language.Compile (BuilderState (..), ExprM, runCircuitBuilder)
import Data.Aeson (decodeFileStrict)
import Data.Aeson qualified as A
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Binary (decodeFile, encodeFile)
import Data.ByteString.Lazy qualified as LBS
import Data.Field.Galois (PrimeField)
import Data.Text qualified as Text
import Options.Applicative (CommandFields, Mod, Parser, ParserInfo, command, execParser, fullDesc, header, help, helper, hsubparser, info, long, progDesc, showDefault, strOption, switch, value)
import Protolude
import R1CS (toR1CS)
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
        <*> hsubparser (compileCommand <> solveCommand)

    compileCommand :: Mod CommandFields Command
    compileCommand =
      command "compile" (info (Compile <$> compileOptsParser <**> helper) (progDesc "Compile the program to an r1cs and constraint system"))

    solveCommand :: Mod CommandFields Command
    solveCommand =
      command "solve" (info (Solve <$> solveOptsParser <**> helper) (progDesc "Generate a witness"))

data Command = Compile CompileOpts | Solve SolveOpts

data CompileOpts = CompileOpts
  { optimizeOpts :: OptimizeOpts,
    includeJson :: Bool
  }

compileOptsParser :: Parser CompileOpts
compileOptsParser =
  CompileOpts
    <$> optimizeOptsParser
    <*> switch
      ( long "json"
          <> help "also write json versions of artifacts"
      )

data OptimizeOpts = OptimizeOpts
  { propogateConstants :: Bool,
    removeUnreachable :: Bool
  }

optimizeOptsParser :: Parser OptimizeOpts
optimizeOptsParser =
  OptimizeOpts
    <$> switch
      ( long "propogate-constants"
          <> help "propogate constants through the circuit"
      )
    <*> switch
      ( long "remove-unreachable"
          <> help "detect and remove variables not contributing to the output"
      )

data SolveOpts = SolveOpts
  { inputsFile :: FilePath
  }

solveOptsParser :: Parser SolveOpts
solveOptsParser =
  SolveOpts
    <$> strOption
      ( long "inputs"
          <> help "inputs json file"
          <> showDefault
          <> value "inputs.json"
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
    Compile _ -> do
      let BuilderState {..} = snd $ runCircuitBuilder program
          prog = mkCircomProgram bsVars bsCircuit
          r1cs = r1csToCircomR1CS $ toR1CS (cpVars prog) (cpCircuit prog)
      createDirectoryIfMissing True (outputDir opts)
      encodeFile (r1csFilePath $ outputDir opts) r1cs
      encodeFile (binFilePath $ outputDir opts) prog
      let inputsTemplate = map (const A.Null) $ labelToVar $ cvInputsLabels $ cpVars prog
      LBS.writeFile (inputsTemplateFilePath $ outputDir opts) (encodePretty $ inputsTemplate)
    Solve solveOpts -> do
      inputs <- do
        mInputs <- decodeFileStrict (inputsFile solveOpts)
        maybe (panic "Failed to decode inputs") (pure . map (fromInteger @f)) mInputs
      circuit <- decodeFile (binFilePath $ outputDir opts)
      let wtns = nativeGenWitness circuit inputs
      encodeFile (witnessFilePath $ outputDir opts) wtns
  where
    baseFilePath :: FilePath -> FilePath
    baseFilePath dir = dir <> "/" <> Text.unpack progName
    inputsTemplateFilePath dir = dir <> "/" <> "inputs-template.json"
    binFilePath dir = baseFilePath dir <> ".bin"
    r1csFilePath dir = baseFilePath dir <> ".r1cs"
    witnessFilePath dir = baseFilePath dir <> ".wtns"
