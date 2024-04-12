{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Circuit
import Data.Binary (encodeFile)
import Data.Field.Galois (GaloisField, Prime)
import Data.Map qualified as Map
import Data.Propagator (Propagated, PropagatedNum)
import Protolude
import R1CS (calculateWitness, isValidWitness)
import R1CS.Circom (r1csToCircomR1CS, witnessToCircomWitness)

main :: IO ()
main = do
  let BuilderState {..} = snd $ runCircuitBuilder $ program @Fr
      publicInputs = Map.fromList $ zip bsPublicInputs [6]
      privateInputs = Map.fromList $ zip bsPrivateInputs [2, 3]
      inputs = publicInputs <> privateInputs
      (r1cs, wtns) = calculateWitness inputs bsCircuit
  unless (isValidWitness wtns r1cs) $ panic "Invalid witness"
  encodeFile "circom-compat/examples/factors/circuit.r1cs" $ r1csToCircomR1CS r1cs
  encodeFile "circom-compat/examples/factors/witness.wtns" $ witnessToCircomWitness wtns

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

instance (KnownNat p) => Propagated (Prime p)

instance (KnownNat p) => PropagatedNum (Prime p)

program :: (GaloisField f) => ExprM f Wire
program = do
  n <- deref <$> freshPublicInput
  a <- deref <$> freshPrivateInput
  b <- deref <$> freshPrivateInput
  let isFactorization = eq n (a `mul` b)
  ret $ cond isFactorization (c 1) (c 0)