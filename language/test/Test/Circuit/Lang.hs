{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Circuit.Lang where

import Circuit
import Circuit.Language
import Data.Field.Galois (Prime, PrimeField (fromP))
import Data.Finite (Finite)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Protolude hiding (Show, show)
import Test.QuickCheck (Property, (==>))

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

type instance NBits (Prime p) = 254

nBits :: Int
nBits = 254

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
  (x /= y) ==>
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

bitIndex :: Finite (NBits Fr) -> ExprM Fr Wire
bitIndex i = do
  x <- deref <$> fieldInput Public "x"
  let bits = splitBits x
  retBool "out" $ atIndex bits i

prop_bitIndex :: Int -> Fr -> Bool
prop_bitIndex i x =
  let _i = i `mod` nBits
      _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (bitIndex $ fromIntegral _i)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
   in (fieldToBool <$> lookupVar bsVars "out" w) == Just (testBit _x _i)

setAtIndex :: Finite (NBits Fr) -> Bool -> ExprM Fr Wire
setAtIndex i b = do
  x <- deref <$> fieldInput Public "x"
  let bits = splitBits x
      bits' = updateIndex_ i (cBool b) bits
  retField "out" $ joinBits bits'

prop_setAtIndex :: Int -> Fr -> Bool -> Bool
prop_setAtIndex i x b =
  let _i = i `mod` nBits
      _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (setAtIndex (fromIntegral _i) b)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
   in res == Just (fromInteger $ if b then setBit _x _i else clearBit _x _i)

-- TODO: investigate why this one is SCARY SLOW
bundleUnbundle :: ExprM Fr Wire
bundleUnbundle = do
  x <- deref <$> fieldInput Public "x"
  b <- unBundle $ splitBits x
  let res = sum b
  retField "out" res

prop_bundleUnbundle :: Fr -> Bool
prop_bundleUnbundle x =
  let _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bundleUnbundle
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = foldl (\acc i -> acc + if testBit _x i then 1 else 0) 0 [0 .. nBits - 1]
   in res == Just (fromInteger expected)

sharingProg :: ExprM Fr Wire
sharingProg = do
  x <- deref <$> fieldInput Public "x"
  y <- deref <$> fieldInput Public "y"
  let z = x * y
  retField "out" $ sum $ replicate 10 z

prop_sharingProg :: Fr -> Fr -> Bool
prop_sharingProg x y =
  let _x = fromP x
      _y = fromP y
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder sharingProg
      input = assignInputs bsVars $ Map.fromList [("x", x), ("y", y)]
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = fromInteger $ sum $ replicate 10 (_x * _y)
   in res == Just expected

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
