{-# LANGUAGE DataKinds #-}

module Test.Circuit.Expr where

import Circuit
import Data.Field.Galois (Prime)
import Data.Map qualified as Map
import Protolude hiding (Show, show)
import Test.Circuit.Affine
import Test.Tasty.QuickCheck
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Prelude (Show (..))

-------------------------------------------------------------------------------
-- Generators
-------------------------------------------------------------------------------

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

arbExprBool :: (Arbitrary f, Num f) => Int -> Int -> Gen (Signal f Bool)
arbExprBool numVars size
  | size <= 0 =
      oneof $
        [EVal . ValBool <$> oneof [pure 0, pure 1]]
          ++ if numVars > 0
            then []
            else []
  | otherwise =
      oneof
        [ EBinOp BAnd
            <$> arbExprBool numVars (size - 1)
            <*> arbExprBool
              numVars
              (size - 1),
          EBinOp BOr
            <$> arbExprBool numVars (size - 1)
            <*> arbExprBool
              numVars
              (size - 1),
          EUnOp UNot <$> arbExprBool numVars (size - 1),
          EEq
            <$> arbExpr numVars (size - 1)
            <*> arbExpr numVars (size - 1)
        ]

arbExpr :: (Arbitrary f, Num f) => Int -> Int -> Gen (Signal f f)
arbExpr numVars size
  | size <= 0 =
      oneof $
        [EVal . ValField <$> arbitrary]
          ++ if numVars > 0
            then [EVar . VarField . InputWire "" Public <$> choose (0, numVars - 1)]
            else []
  | otherwise =
      oneof
        [ EBinOp BAdd <$> arbExpr numVars (size - 1) <*> arbExpr numVars (size - 1),
          EBinOp BSub <$> arbExpr numVars (size - 1) <*> arbExpr numVars (size - 1),
          EBinOp BMul <$> arbExpr numVars (size - 1) <*> arbExpr numVars (size - 1),
          EUnOp UNeg <$> arbExpr numVars (size - 1),
          EIf
            <$> arbExprBool numVars (size - 1)
            <*> arbExpr numVars (size - 1)
            <*> arbExpr numVars (size - 1)
        ]

data ExprWithInputs f = ExprWithInputs (Signal f f) [Map Int f]

instance (Arbitrary f, Num f) => Arbitrary (ExprWithInputs f) where
  arbitrary = do
    numVars <- abs <$> arbitrary
    program <- scale (`div` 10) $ sized (arbExpr numVars)
    inputs <- vectorOf 5 $ arbInputVector numVars
    pure $ ExprWithInputs program inputs

instance (Pretty f) => Show (ExprWithInputs f) where
  show (ExprWithInputs expr inputs) = show $ pretty expr <+> pretty (Map.toList <$> inputs)

-------------------------------------------------------------------------------
-- Tests
-------------------------------------------------------------------------------

-- | Check whether exprToArithCircuit produces valid circuits
prop_compiledCircuitValid :: ExprWithInputs Fr -> Bool
prop_compiledCircuitValid (ExprWithInputs expr _) =
  validArithCircuit (execCircuitBuilder $ exprToArithCircuit expr (Identity $ OutputWire 0))

-- | Check whether evaluating an expression and
-- evaluating the arithmetic circuit translation produces the same
-- result
prop_evalEqArithEval :: ExprWithInputs Fr -> Bool
prop_evalEqArithEval (ExprWithInputs expr inputs) = all testInput inputs
  where
    testInput input =
      let a = runIdentity $ evalExpr (Map.mapKeys (InputWire "" Public) input) expr
          b = arithResult input
       in a == b
    arithResult input = arithOutput input Map.! (OutputWire 1)
    arithOutput input =
      evalArithCircuit
        (Map.lookup)
        (Map.insert)
        circuit
        (Map.mapKeys (InputWire "" Public) input)
    circuit = (execCircuitBuilder $ exprToArithCircuit expr (Identity $ OutputWire 1))
