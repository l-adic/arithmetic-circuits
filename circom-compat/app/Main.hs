{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Circuit
import Data.Binary (encodeFile)
import Data.Field.Galois (GaloisField, Prime)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Protolude
import R1CS (Inputs (..), calculateWitness, isValidWitness)
import R1CS.Circom (r1csToCircomR1CS, witnessToCircomWitness)

main :: IO ()
main = do
  let BuilderState {..} = snd $ runCircuitBuilder $ program @Fr
      publicInputs = Map.fromList $ zip (Set.toAscList $ cvPublicInputs bsVars) [6]
      privateInputs = Map.fromList $ zip (Set.toAscList $ cvPrivateInputs bsVars) [2, 3]
      inputs = publicInputs <> privateInputs
      (r1cs, wtns) = calculateWitness bsVars bsCircuit (Inputs inputs)
  unless (isValidWitness wtns r1cs) $ panic "Invalid witness"
  encodeFile "circom-compat/examples/factors/circuit.r1cs" $ r1csToCircomR1CS r1cs
  encodeFile "circom-compat/examples/factors/witness.wtns" $ witnessToCircomWitness wtns

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

program :: (GaloisField f) => ExprM f Wire
program = do
  n <- deref <$> fieldInput Public "n"
  a <- deref <$> fieldInput Private "a"
  b <- deref <$> fieldInput Private "b"
  retBool "out" $ eq n (a * b)
