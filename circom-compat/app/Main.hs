module Main where

import Circuit
import Circuit.Language
import Circuit.Solver.Circom (CircomProgram (..), mkCircomProgram, nativeGenWitness)
import Data.Binary (decodeFile, encodeFile)
import Data.Field.Galois (Prime)
import Data.Map qualified as Map
import Protolude
import R1CS (toR1CS)
import R1CS.Circom (r1csToCircomR1CS)

main :: IO ()
main = do
  let BuilderState {..} = snd $ runCircuitBuilder program
      prog = mkCircomProgram bsVars bsCircuit
      r1cs = r1csToCircomR1CS $ toR1CS (cpVars prog) (cpCircuit prog)
      inputs = Map.fromList [("n", 6), ("a", 2), ("b", 3)]
      wtns = nativeGenWitness prog inputs
  encodeFile "circom-compat/examples/factors/circuit.r1cs" r1cs
  encodeFile "circom-compat/examples/factors/circuit.bin" prog
  encodeFile "circom-compat/examples/factors/witness.wtns" wtns
  prog' <- decodeFile "circom-compat/examples/factors/circuit.bin"
  print $ nativeGenWitness prog' inputs == wtns

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

program :: ExprM Fr (Var Wire Fr 'TBool)
program = do
  n <- var_ <$> fieldInput Public "n"
  a <- var_ <$> fieldInput Private "a"
  b <- var_ <$> fieldInput Private "b"
  boolOutput "out" $ eq_ n (a * b)
