{-#LANGUAGE DataKinds #-}
module Test.Circuit.Arithmetic where

import           Circuit.Affine
import           Circuit.Arithmetic
import qualified Data.Map                     as Map
import           Protolude
import           Test.Tasty.QuickCheck
import Data.Field.Galois (Prime)

-------------------------------------------------------------------------------
-- Test values
-------------------------------------------------------------------------------

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

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

arbVars :: Int -> [Int] -> [Gen (AffineCircuit Wire f)]
arbVars numInps mids =
  varInps numInps ++ varMids mids
  where
    varInps size
      | size <= 0 = []
      | otherwise = [Var . InputWire <$> choose (0, numInps - 1)]
    varMids [] = []
    varMids ms@(_ : _) = [Var . IntermediateWire <$> elements ms]

arbAffineCircuitWithMids ::
  Arbitrary f =>
  Int ->
  [Int] ->
  Int ->
  Gen (AffineCircuit Wire f)
arbAffineCircuitWithMids numInps mids size
  | size <= 0 =
    oneof $ [ConstGate <$> arbitrary] ++ arbVars numInps mids
  | otherwise =
    oneof
      [ ScalarMul <$> arbitrary <*> arbAffineCircuitWithMids numInps mids (size - 1),
        Add <$> arbAffineCircuitWithMids numInps mids (size - 1)
          <*> arbAffineCircuitWithMids numInps mids (size - 1)
      ]

arbInputVector :: (Arbitrary f) => Int -> Gen (Map Int f)
arbInputVector numVars = Map.fromList . zip [0 ..] <$> vector numVars

arbArithCircuit ::
  Arbitrary f =>
  -- | distribution of frequency of mul/equal/split
  -- gates, respectively
  (Int, Int, Int) ->
  Int ->
  Int ->
  Gen (ArithCircuit f)
arbArithCircuit (distMul, distEqual, distSplit) numInps size
  | size <= 0 =
    pure $ ArithCircuit []
  | otherwise =
    do
      ArithCircuit gates <- arbArithCircuit (distMul, distEqual, distSplit) numInps (size - 1)
      let mids = [i | IntermediateWire i <- concatMap outputWires gates]
      frequency . catMaybes $
        [ (distMul,) <$> mulGate gates mids,
          (distEqual,) <$> equalGate gates mids,
          (distSplit,) <$> splitGate gates mids
        ]
  where
    mulGate gates mids =
      Just $ do
        lhs <- arbAffineCircuitWithMids numInps mids 1
        rhs <- arbAffineCircuitWithMids numInps mids 1
        let outWire = case mids of
              [] -> 0
              ms@(_ : _) -> maximum ms + 1
            gate = Mul lhs rhs (IntermediateWire outWire)
        pure . ArithCircuit $ gates ++ [gate]
    equalGate _ [] =
      Nothing
    equalGate gates mids@(_ : _) =
      Just $ do
        inp <- elements mids
        let outWire = maximum mids + 1
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
        let firstOutWire = maximum mids + 1
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
    numVars <- abs <$> arbitrary `suchThat` (> 0)
    program <- sized (arbArithCircuit (50, 10, 1) numVars)
    inputs <- vectorOf 5 $ arbInputVector numVars
    pure $ ArithCircuitWithInputs program inputs

data ArithCircuitWithInput f = ArithCircuitWithInput (ArithCircuit f) (Map Int f)
  deriving (Show, Generic, NFData)

instance (Arbitrary f, Num f) => Arbitrary (ArithCircuitWithInput f) where
  arbitrary = do
    numVars <- abs <$> arbitrary `suchThat` (> 0)
    program <- sized (arbArithCircuit (50, 10, 1) numVars)
    input <- arbInputVector numVars
    pure $ ArithCircuitWithInput program input

-------------------------------------------------------------------------------
-- Tests
-------------------------------------------------------------------------------

prop_arithCircuitValid :: ArithCircuitWithInputs Fr -> Bool
prop_arithCircuitValid (ArithCircuitWithInputs program _) =
  validArithCircuit program