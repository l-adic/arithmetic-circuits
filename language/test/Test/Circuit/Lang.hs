{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoStarIsType #-}

module Test.Circuit.Lang where

import Circuit
import Circuit.Language
import Data.Field.Galois (Prime, PrimeField (fromP))
import Data.Finite (Finite)
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Protolude
import Test.QuickCheck (Property, (.&&.), (=/=), (===), (==>))

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

nBits :: Int
nBits = fromIntegral $ natVal (Proxy @(NBits Fr))

bitSplitJoin :: ExprM Fr (Expr Wire Fr 'TField)
bitSplitJoin = do
  _x <- var_ <$> fieldInput Public "x"
  let res = join_ $ split_ _x
  void $ fieldOutput "out" $ res
  pure res

prop_bitsSplitJoin :: Fr -> Property
prop_bitsSplitJoin x =
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder bitSplitJoin
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupVar bsVars "out" w === Just x .&&. computed === x

prop_bitsSplitJoinContra :: Fr -> Fr -> Property
prop_bitsSplitJoinContra x y =
  (x /= y) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
        input = assignInputs bsVars $ Map.singleton "x" x
        w = solve bsVars bsCircuit input
     in lookupVar bsVars "out" w =/= Just y

factors :: ExprM Fr (Expr Wire Fr 'TBool)
factors = do
  n <- var_ <$> fieldInput Public "n"
  a <- var_ <$> fieldInput Public "a"
  b <- var_ <$> fieldInput Public "b"
  let isFactorization = eq_ n (a * b)
  void $ boolOutput "out" isFactorization
  pure isFactorization

prop_factorization :: Fr -> Fr -> Property
prop_factorization x y =
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder factors
      inputs = assignInputs bsVars $ Map.fromList [("n", x * y), ("a", x), ("b", y)]
      w = solve bsVars bsCircuit inputs
      computed = evalExpr IntMap.lookup inputs (relabelExpr wireName prog)
   in lookupVar bsVars "out" w === Just 1 .&&. computed === True

prop_factorizationContra :: Fr -> Fr -> Fr -> Property
prop_factorizationContra x y z =
  (x * y /= z) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder factors
        inputs = assignInputs bsVars $ Map.fromList [("n", z), ("a", x), ("b", y)]
        w = solve bsVars bsCircuit inputs
     in lookupVar bsVars "out" w == Just 0

bitIndex :: Finite (NBits Fr) -> ExprM Fr (Expr Wire Fr 'TBool)
bitIndex i = do
  x <- var_ <$> fieldInput Public "x"
  let bits = split_ x
  bi <- atIndex i bits
  void $ boolOutput "out" bi
  pure bi

prop_bitIndex :: Int -> Fr -> Property
prop_bitIndex i x =
  let _i = i `mod` nBits
      _x = fromP x
      (_, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (bitIndex $ fromIntegral _i)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      expected = if testBit _x _i then 1 else 0
   in lookupVar bsVars "out" w === Just expected

setAtIndex :: Finite (NBits Fr) -> Bool -> ExprM Fr (Expr Wire Fr 'TField)
setAtIndex i b = do
  x <- var_ <$> fieldInput Public "x"
  let bits = split_ x
  bits' <- updateIndex_ i (cBool b) bits
  let res = join_ bits'
  void $ fieldOutput "out" res
  pure res

prop_setAtIndex :: Int -> Fr -> Bool -> Property
prop_setAtIndex i x b =
  let _i = i `mod` nBits
      _x = fromP x
      (_, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (setAtIndex (fromIntegral _i) b)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = fromInteger (if b then setBit _x _i else clearBit _x _i)
   in res === Just expected

-- TODO: investigate why this one is SCARY SLOW
bundleUnbundle :: ExprM Fr (Expr Wire Fr 'TField)
bundleUnbundle = do
  x <- var_ <$> fieldInput Public "x"
  bits <- unbundle $ split_ x
  let negated = map not_ bits
  let res = unAdd_ $ foldMap (Add_ . boolToField) negated
  void $ fieldOutput "out" res
  pure res

prop_bundleUnbundle :: Fr -> Property
prop_bundleUnbundle x =
  let _x = fromP x
      (_, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder bundleUnbundle
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = foldl (\acc i -> acc + if testBit _x i then 0 else 1) 0 [0 .. nBits - 1]
   in res === Just expected

sharingProg :: ExprM Fr (Expr Wire Fr 'TField)
sharingProg = do
  x <- var_ <$> fieldInput Public "x"
  y <- var_ <$> fieldInput Public "y"
  let z = sum $ replicate 10 (x * y)
  void $ fieldOutput "out" z
  pure $ z

prop_sharingProg :: Fr -> Fr -> Property
prop_sharingProg x y =
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (sharingProg)
      input = assignInputs bsVars $ Map.fromList [("x", x), ("y", y)]
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = sum $ replicate 10 (x * y)
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in res === Just expected .&&. computed === expected

--------------------------------------------------------------------------------
