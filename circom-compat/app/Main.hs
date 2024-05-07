{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Circuit
import Circuit.Language
import Data.Binary (encodeFile)
import Data.Field.Galois (Prime)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Protolude
import R1CS (Inputs (..), calculateWitness, isValidWitness)
import R1CS.Circom (r1csToCircomR1CS, witnessToCircomWitness)

main :: IO ()
main = do
  let BuilderState {..} = snd $ runCircuitBuilder program
      publicInputs = IntMap.fromList $ zip (IntSet.toAscList $ cvPublicInputs bsVars) [6]
      privateInputs = IntMap.fromList $ zip (IntSet.toAscList $ cvPrivateInputs bsVars) [2, 3]
      inputs = publicInputs <> privateInputs
      (r1cs, wtns) = calculateWitness bsVars bsCircuit (Inputs inputs)
  unless (isValidWitness wtns r1cs) $ panic "Invalid witness"
  encodeFile "circom-compat/examples/factors/circuit.r1cs" $ r1csToCircomR1CS r1cs
  encodeFile "circom-compat/examples/factors/witness.wtns" $ witnessToCircomWitness wtns

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

program :: ExprM Fr (Var Wire Fr 'TBool)
program = do
  n <- var_ <$> fieldInput Public "n"
  a <- var_ <$> fieldInput Private "a"
  b <- var_ <$> fieldInput Private "b"
  boolOutput "out" $ eq_ n (a * b)
