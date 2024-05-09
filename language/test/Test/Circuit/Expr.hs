{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}

module Test.Circuit.Expr where

import Circuit
import Circuit.Language
import Data.Field.Galois (GaloisField, Prime)
import Data.Map qualified as Map
import Data.Vector qualified as V
import Protolude hiding (Show, show)
import Test.Tasty.QuickCheck
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Prelude (Show (..))

-------------------------------------------------------------------------------
-- Generators
-------------------------------------------------------------------------------

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

arbExprBool :: (GaloisField f, Hashable f) => Int -> Int -> Gen (Signal f 'TBool)
arbExprBool numVars size
  | size <= 0 =
      oneof $
        [val_ . ValBool <$> oneof [pure 0, pure 1]]
          ++ if numVars > 0
            then []
            else []
  | otherwise =
      oneof
        [ binOp_ BAnd
            <$> arbExprBool numVars (size - 1)
            <*> arbExprBool
              numVars
              (size - 1),
          binOp_ BOr
            <$> arbExprBool numVars (size - 1)
            <*> arbExprBool
              numVars
              (size - 1),
          unOp_ UNot <$> arbExprBool numVars (size - 1),
          eq_
            <$> arbExpr numVars (size - 1)
            <*> arbExpr numVars (size - 1)
        ]

arbExpr :: (GaloisField f, Hashable f) => Int -> Int -> Gen (Signal f 'TField)
arbExpr numVars size
  | size <= 0 =
      oneof $
        [val_ . ValField <$> arbitrary]
          ++ if numVars > 0
            then [var_ . VarField . InputWire "" Public <$> choose (0, numVars - 1)]
            else []
  | otherwise =
      oneof
        [ binOp_ BAdd <$> arbExpr numVars (size - 1) <*> arbExpr numVars (size - 1),
          binOp_ BSub <$> arbExpr numVars (size - 1) <*> arbExpr numVars (size - 1),
          binOp_ BMul <$> arbExpr numVars (size - 1) <*> arbExpr numVars (size - 1),
          unOp_ UNeg <$> arbExpr numVars (size - 1),
          if_
            <$> arbExprBool numVars (size - 1)
            <*> arbExpr numVars (size - 1)
            <*> arbExpr numVars (size - 1)
        ]

data ExprWithInputs f = ExprWithInputs (Signal f 'TField) [Map Int f]

instance (GaloisField f, Hashable f) => Arbitrary (ExprWithInputs f) where
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
  validArithCircuit $ execCircuitBuilder (exprToArithCircuit expr (OutputWire 0))

-- | Check whether evaluating an expression and
-- evaluating the arithmetic circuit translation produces the same
-- result
prop_evalEqArithEval :: ExprWithInputs Fr -> Bool
prop_evalEqArithEval (ExprWithInputs expr inputs) =
  let circuit = (execCircuitBuilder $ exprToArithCircuit expr (OutputWire 1))
   in all (testInput circuit) inputs
  where
    testInput circuit input =
      let a = evalExpr Map.lookup (Map.mapKeys (InputWire "" Public) input) expr
          b = arithOutput input circuit Map.! (OutputWire 1)
       in a == Right (V.singleton b)
    arithOutput input circuit =
      evalArithCircuit
        (Map.lookup)
        (Map.insert)
        circuit
        (Map.mapKeys (InputWire "" Public) input)

arbInputVector :: (Arbitrary f) => Int -> Gen (Map Int f)
arbInputVector numVars = Map.fromList . zip [0 ..] <$> vector numVars
