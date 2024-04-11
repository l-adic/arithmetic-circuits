{-#LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Circuit.Arithmetic where

import           Circuit.Affine
import           Circuit.Arithmetic
import qualified Data.Map                     as Map
import           Protolude
import           Test.Tasty.QuickCheck
import Data.Field.Galois (Prime)
import Circuit.Solver
import Data.Propagator (PropagatedNum, Propagated)
import Data.List ((\\))

-------------------------------------------------------------------------------
-- Test values
-------------------------------------------------------------------------------

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

instance KnownNat p => Propagated (Prime p)
instance KnownNat p => PropagatedNum (Prime p)

testEqualCircuit :: ArithCircuit Fr
testEqualCircuit = ArithCircuit [Equal (InputWire 0) (IntermediateWire 0) (OutputWire 0)]

testInputMap :: Fr -> Map Int Fr
testInputMap = Map.singleton 0

testSplitUnsplitCircuit :: Int -> ArithCircuit Fr
testSplitUnsplitCircuit nbits =
  ArithCircuit
    [ Split (InputWire 0) midWires,
      Mul (ConstGate 1) (unsplit midWires) (OutputWire 0)
    ]
  where
    midWires = fmap IntermediateWire [0 .. nbits - 1]

-------------------------------------------------------------------------------
-- Generators
-------------------------------------------------------------------------------

arbVars :: [Int] -> [Int] -> [Gen (AffineCircuit f Wire)]
arbVars inputs mids =
  varInps inputs ++ varMids (mids \\ inputs)
  where
    varInps _inputs = [Var . InputWire <$> elements _inputs]
    varMids [] = []
    varMids ms@(_ : _) = [Var . IntermediateWire <$> elements ms]

arbAffineCircuitWithMids ::
  Arbitrary f =>
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
        Add <$> arbAffineCircuitWithMids inputs mids (size - 1)
          <*> arbAffineCircuitWithMids inputs mids (size - 1)
      ]

arbInputVector :: (Arbitrary f) => Int -> Gen (Map Int f)
arbInputVector numVars = Map.fromList . zip [0 ..] <$> vector numVars

arbArithCircuit ::
  Arbitrary f =>
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
    program <- sized (arbArithCircuit (50, 10, 1) [0 .. numInputs - 1])
    inputs <- vectorOf 5 $ arbInputVector numInputs
    pure $ ArithCircuitWithInputs program inputs

data ArithCircuitWithInput f = ArithCircuitWithInput (ArithCircuit f) (Map Int f)
  deriving (Show, Generic, NFData)

instance (Arbitrary f, Num f) => Arbitrary (ArithCircuitWithInput f) where
  arbitrary = do
    numInputs <- abs <$> arbitrary `suchThat` (> 0)
    program <- sized (arbArithCircuit (50, 10, 1) [0 .. numInputs - 1])
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
  solve inputs program  == 
    evalArithCircuit 
        (\w m -> Map.lookup (wireName w) m)
        (\w m -> Map.insert (wireName w) m)
        program
        inputs