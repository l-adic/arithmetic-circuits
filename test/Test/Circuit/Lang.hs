{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -freduction-depth=0 #-}

module Test.Circuit.Lang where

import Circuit
import Data.Field.Galois (Prime, PrimeField (fromP))
import Data.Fin (Fin)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Protolude hiding (Show, show)
import Test.QuickCheck (Property, (==>))

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

type instance NBits (Prime p) = FromGHC 256

bitSplitJoin :: ExprM Fr Wire
bitSplitJoin = do
  _x <- deref <$> fieldInput Public "x"
  retField "out" $ joinBits $ splitBits _x

prop_bitsSplitJoin :: Fr -> Bool
prop_bitsSplitJoin x =
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
   in lookupVar bsVars "out" w == Just x

prop_bitsSplitJoinContra :: Fr -> Fr -> Property
prop_bitsSplitJoinContra x y =
  x /= y ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
        input = assignInputs bsVars $ Map.singleton "x" x
        w = solve bsVars bsCircuit input
     in fromJust (lookupVar bsVars "out" w) /= y

factors :: ExprM Fr Wire
factors = do
  n <- deref <$> fieldInput Public "n"
  a <- deref <$> fieldInput Public "a"
  b <- deref <$> fieldInput Public "b"
  let isFactorization = eq n (a * b)
  retBool "out" isFactorization

prop_factorization :: Fr -> Fr -> Bool
prop_factorization x y =
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder factors
      inputs = assignInputs bsVars $ Map.fromList [("n", x * y), ("a", x), ("b", y)]
      w = solve bsVars bsCircuit inputs
   in lookupVar bsVars "out" w == Just 1

prop_factorizationContra :: Fr -> Fr -> Fr -> Property
prop_factorizationContra x y z =
  (x * y /= z) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder factors
        inputs = assignInputs bsVars $ Map.fromList [("n", z), ("a", x), ("b", y)]
        w = solve bsVars bsCircuit inputs
     in lookupVar bsVars "out" w == Just 0

bitIndex :: Fin (NBits Fr) -> ExprM Fr Wire
bitIndex i = do
  x <- deref <$> fieldInput Public "x"
  let bits = splitBits x
  retBool "out" $ atIndex bits i

prop_bitIndex :: Int -> Fr -> Bool
prop_bitIndex i x =
  let _i = i `mod` 256
      _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (bitIndex $ fromIntegral _i)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
   in (fieldToBool <$> lookupVar bsVars "out" w) == Just (testBit _x _i)

--------------------------------------------------------------------------------

fieldToBool :: Fr -> Bool
fieldToBool x = x /= 0

lookupVar :: CircuitVars Text -> Text -> Map Int f -> Maybe f
lookupVar vs label sol = do
  var <- Map.lookup label (cvInputsLabels vs)
  Map.lookup var sol

assignInputs :: CircuitVars Text -> Map Text f -> Map Int f
assignInputs CircuitVars {..} inputs =
  let res =
        Map.fromList
          [ (var, val)
            | (l1, var) <- Map.toList cvInputsLabels,
              (l2, val) <- Map.toList inputs,
              l1 == l2
          ]
   in if Map.size inputs /= Map.size res
        then panic "Some inputs are missing"
        else res
