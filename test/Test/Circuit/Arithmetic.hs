{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Circuit.Arithmetic where

import Circuit.Affine
import Circuit.Arithmetic
import Circuit.Solver
import Data.Field.Galois (Prime, char, fromP)
import Data.List ((\\))
import Data.Map qualified as Map
import Data.Propagator (Propagated, PropagatedNum)
import Math.NumberTheory.Logarithms (naturalLog2)
import Protolude
import Test.Tasty.QuickCheck

-------------------------------------------------------------------------------
-- Test values
-------------------------------------------------------------------------------

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

instance (KnownNat p) => Propagated (Prime p)

instance (KnownNat p) => PropagatedNum (Prime p)

-------------------------------------------------------------------------------
-- Generators
-------------------------------------------------------------------------------

arbVars :: [Int] -> [Int] -> [Gen (AffineCircuit f Wire)]
arbVars inputs mids =
  varInps inputs ++ varMids (mids \\ inputs)
  where
    varInps _inputs = [Var . InputWire "" Public <$> elements _inputs]
    varMids [] = []
    varMids ms@(_ : _) = [Var . IntermediateWire <$> elements ms]

arbAffineCircuitWithMids ::
  (Arbitrary f) =>
  [Int] ->
  [Int] ->
  Int ->
  Gen (AffineCircuit f Wire)
arbAffineCircuitWithMids inputs mids size
  | size <= 0 =
      oneof $ [ConstGate <$> arbitrary] ++ arbVars inputs mids
  | otherwise =
      oneof
        [ ScalarMul <$> arbitrary <*> arbAffineCircuitWithMids inputs mids (size - 1),
          Add
            <$> arbAffineCircuitWithMids inputs mids (size - 1)
            <*> arbAffineCircuitWithMids inputs mids (size - 1)
        ]

arbInputVector :: (Arbitrary f) => Int -> Gen (Map Int f)
arbInputVector numVars = Map.fromList . zip [1 ..] <$> vector numVars

arbArithCircuit ::
  (Arbitrary f) =>
  -- | distribution of frequency of mul/equal/split
  -- gates, respectively
  (Int, Int, Int) ->
  [Int] ->
  Int ->
  Gen (ArithCircuit f)
arbArithCircuit (distMul, distEqual, distSplit) inputs size
  | size <= 0 =
      pure $ ArithCircuit []
  | otherwise =
      do
        ArithCircuit gates <- arbArithCircuit (distMul, distEqual, distSplit) inputs (size - 1)
        let mids =
              [i | IntermediateWire i <- concatMap outputWires gates]

        frequency . catMaybes $
          [ (distMul,) <$> mulGate gates mids,
            (distEqual,) <$> equalGate gates mids,
            (distSplit,) <$> splitGate gates mids
          ]
  where
    mulGate gates mids =
      Just $ do
        lhs <- arbAffineCircuitWithMids inputs mids 1
        rhs <- arbAffineCircuitWithMids inputs mids 1
        let outWire = case mids of
              [] -> maximum inputs + 1
              ms@(_ : _) -> maximum (ms <> inputs) + 1
            gate = Mul lhs rhs (IntermediateWire outWire)
        pure . ArithCircuit $ gates ++ [gate]
    equalGate _ [] =
      Nothing
    equalGate gates mids@(_ : _) =
      Just $ do
        inp <- elements mids
        let outWire = maximum (mids <> inputs) + 1
            gate =
              Equal
                (IntermediateWire inp)
                (IntermediateWire outWire)
                (IntermediateWire $ outWire + 1)
        pure . ArithCircuit $ gates ++ [gate]
    splitGate _ [] =
      Nothing
    splitGate gates mids@(_ : _) =
      Just $ do
        inp <- IntermediateWire <$> elements mids
        let firstOutWire = maximum (mids <> inputs) + 1
            nbits = 256
            outWires = fmap IntermediateWire [firstOutWire .. firstOutWire + nbits - 1]
            gate = Split inp outWires
        pure . ArithCircuit $ gates ++ [gate]

-- | The input vector has to have the correct length, so we want to
-- generate the program and the test input simultaneously.
data ArithCircuitWithInputs f = ArithCircuitWithInputs (ArithCircuit f) [Map Int f]
  deriving (Show, Generic, NFData)

instance (Arbitrary f, Num f) => Arbitrary (ArithCircuitWithInputs f) where
  arbitrary = do
    numInputs <- abs <$> arbitrary `suchThat` (> 0)
    program <- sized (arbArithCircuit (50, 10, 1) [1 .. numInputs])
    inputs <- vectorOf 5 $ arbInputVector numInputs
    pure $ ArithCircuitWithInputs program inputs

data ArithCircuitWithInput f = ArithCircuitWithInput (ArithCircuit f) (Map Int f)
  deriving (Show, Generic, NFData)

instance (Arbitrary f, Num f) => Arbitrary (ArithCircuitWithInput f) where
  arbitrary = do
    numInputs <- abs <$> arbitrary `suchThat` (> 0)
    program <- sized (arbArithCircuit (50, 10, 1) [1 .. numInputs])
    input <- arbInputVector numInputs
    pure $ ArithCircuitWithInput program input

-------------------------------------------------------------------------------
-- Tests
-------------------------------------------------------------------------------

prop_arithCircuitValid :: ArithCircuitWithInputs Fr -> Bool
prop_arithCircuitValid (ArithCircuitWithInputs program _) =
  validArithCircuit program

prop_equivalentSolver :: ArithCircuitWithInput Fr -> Bool
prop_equivalentSolver (ArithCircuitWithInput program inputs) =
  solve inputs program
    == evalArithCircuit
      (\w m -> Map.lookup (wireName w) m)
      (\w m -> Map.insert (wireName w) m)
      program
      inputs

prop_basicMultiplication :: (Fr, Fr) -> Bool
prop_basicMultiplication (a, b) =
  let c = ArithCircuit [Mul (Var (InputWire "" Public 1)) (Var (InputWire "" Public 2)) (OutputWire 3)]
      inputs = Map.fromList [(1, a), (2, b)]
      solution = solve inputs c
   in Map.lookup 3 solution == Just (a * b)

prop_complexMultiplication :: (Fr, Fr, Fr, Fr) -> Bool
prop_complexMultiplication (a, b, c, d) =
  let circuit =
        ArithCircuit
          [ Mul (Var (InputWire "" Public 1)) (Var (InputWire "" Public 2)) (OutputWire 3),
            Mul (Var (InputWire "" Public 4)) (Var (InputWire "" Public 5)) (OutputWire 6),
            Mul (Var (OutputWire 3)) (Var (OutputWire 6)) (OutputWire 7)
          ]
      inputs = Map.fromList [(1, a), (2, b), (4, c), (5, d)]
      solution = solve inputs circuit
   in Map.lookup 7 solution == Just (a * b * c * d)

prop_division :: (Fr, Fr) -> Bool
prop_division (a, b) =
  let circuit =
        ArithCircuit
          [ Mul (Var (InputWire "" Public 1)) (Var (InputWire "" Public 5)) (IntermediateWire 3),
            Mul (ConstGate 1) (ConstGate 1) (IntermediateWire 4),
            Mul (Var (InputWire "" Public 2)) (Var (IntermediateWire 5)) (OutputWire 4)
          ]
      inputs = Map.fromList [(1, a), (2, b)]
      solution = solve inputs circuit
   in Map.lookup 3 solution == Just (a / b)

nBits :: Int
nBits = 1 + naturalLog2 (char (1 :: Fr))

prop_bitSummingForward :: Fr -> Bool
prop_bitSummingForward a =
  let circuit =
        ArithCircuit
          [ Split (InputWire "" Public 1) (OutputWire <$> [2 .. nBits + 1])
          ]
      -- forward
      solution = solve (Map.fromList [(1, a)]) circuit
   in all (\i -> Map.lookup i solution == Just (if testBit (fromP a) (i - 2) then 1 else 0)) [2 .. nBits + 1]

prop_bitSummingBackward :: Fr -> Bool
prop_bitSummingBackward a =
  let circuit =
        ArithCircuit
          [ Split (OutputWire 1) (OutputWire <$> [2 .. nBits + 1])
          ]
      -- backward
      solution = solve (Map.fromList $ zip [2 .. nBits + 1] (fmap (\i -> if testBit (fromP a) (i - 2) then 1 else 0) [2 .. nBits + 1])) circuit
   in Map.lookup 1 solution == Just a
