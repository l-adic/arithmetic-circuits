{-# LANGUAGE DataKinds #-}

module Circuit where

import Protolude

import           Circuit.Affine
import           Circuit.Arithmetic
import           Criterion.Main
import qualified Data.Map                     as Map
import Data.Field.Galois (Prime)

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

program :: ArithCircuit Fr
program = ArithCircuit
  [ Mul (Var (InputWire 0)) (Var (InputWire 1)) (IntermediateWire 0)
  , Mul (Var (IntermediateWire 0))(Add (Var (InputWire 0)) (Var (InputWire 2))) (OutputWire 0)
  ]

input :: Map.Map Int Fr
input = Map.fromList [(0, 7), (1, 5), (2, 4)]

benchmarks :: [Benchmark]
benchmarks = []