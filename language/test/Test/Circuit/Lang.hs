{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoStarIsType #-}

module Test.Circuit.Lang where

import Circuit
import Circuit.Language
import Data.Field.Galois (Prime, PrimeField (fromP))
import Data.Finite (Finite)
import Data.Map qualified as Map
import Data.Vector.Sized qualified as SV
import Protolude
import Test.QuickCheck (Property, withMaxSuccess, (=/=), (===), (==>))
import Test.QuickCheck.Monadic (monadicIO, run)
import GHC.TypeNats (Natural, withKnownNat, SNat, withSomeSNat)

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

nBits :: Int
nBits = fromIntegral $ natVal (Proxy @(NBits Fr))

bitSplitJoin :: ExprM Fr (Var Wire Fr Fr)
bitSplitJoin = do
  _x <- deref <$> fieldInput Public "x"
  fieldOutput "out" $ join_ $ split_ _x

prop_bitsSplitJoin :: Fr -> Property
prop_bitsSplitJoin x =
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
   in lookupVar bsVars "out" w === Just x

prop_bitsSplitJoinContra :: Fr -> Fr -> Property
prop_bitsSplitJoinContra x y =
  (x /= y) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
        input = assignInputs bsVars $ Map.singleton "x" x
        w = solve bsVars bsCircuit input
     in lookupVar bsVars "out" w =/= Just y

factors :: ExprM Fr (Var Wire Fr Bool)
factors = do
  n <- deref <$> fieldInput Public "n"
  a <- deref <$> fieldInput Public "a"
  b <- deref <$> fieldInput Public "b"
  let isFactorization = eq_ n (a * b)
  boolOutput "out" isFactorization

prop_factorization :: Fr -> Fr -> Property
prop_factorization x y =
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder factors
      inputs = assignInputs bsVars $ Map.fromList [("n", x * y), ("a", x), ("b", y)]
      w = solve bsVars bsCircuit inputs
   in lookupVar bsVars "out" w === Just 1

prop_factorizationContra :: Fr -> Fr -> Fr -> Property
prop_factorizationContra x y z =
  (x * y /= z) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder factors
        inputs = assignInputs bsVars $ Map.fromList [("n", z), ("a", x), ("b", y)]
        w = solve bsVars bsCircuit inputs
     in lookupVar bsVars "out" w == Just 0

bitIndex :: Finite (NBits Fr) -> ExprM Fr (Var Wire Fr Bool)
bitIndex i = do
  x <- deref <$> fieldInput Public "x"
  let bits = split_ x
  bi <- atIndex i bits
  boolOutput "out" bi

prop_bitIndex :: Int -> Fr -> Property
prop_bitIndex i x =
  let _i = i `mod` nBits
      _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (bitIndex $ fromIntegral _i)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
   in lookupVar bsVars "out" w === Just (if testBit _x _i then 1 else 0)

setAtIndex :: Finite (NBits Fr) -> Bool -> ExprM Fr (Var Wire Fr Fr)
setAtIndex i b = do
  x <- deref <$> fieldInput Public "x"
  let bits = split_ x
  bits' <- updateIndex_ i (cBool b) bits
  fieldOutput "out" $ join_ bits'

prop_setAtIndex :: Int -> Fr -> Bool -> Property
prop_setAtIndex i x b =
  let _i = i `mod` nBits
      _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (setAtIndex (fromIntegral _i) b)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
   in res === Just (fromInteger (if b then setBit _x _i else clearBit _x _i))

-- TODO: investigate why this one is SCARY SLOW
bundleUnbundle :: ExprM Fr (Var Wire Fr Fr)
bundleUnbundle = do
  x <- deref <$> fieldInput Public "x"
  bits <- unbundle $ split_ x
  let negated = map not_ bits
  let res = unAdd_ $ foldMap (Add_ . coerceGroundType) negated
  fieldOutput "out" res

prop_bundleUnbundle :: Fr -> Property
prop_bundleUnbundle x =
  let _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bundleUnbundle
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = foldl (\acc i -> acc + if testBit _x i then 0 else 1) 0 [0 .. nBits - 1]
   in res === Just expected

sharingProg :: ExprM Fr (Var Wire Fr Fr)
sharingProg = do
  x <- deref <$> fieldInput Public "x"
  y <- deref <$> fieldInput Public "y"
  let z = x * y
  fieldOutput "out" $ sum $ replicate 10 z

prop_sharingProg :: Fr -> Fr -> Property
prop_sharingProg x y = monadicIO $ run $ do
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder sharingProg
      input = assignInputs bsVars $ Map.fromList [("x", x), ("y", y)]
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = sum $ replicate 10 (x * y)
  pure $ res === Just expected

largeMult :: forall n. KnownNat n => Proxy n -> ExprM Fr (Var Wire Fr Fr)
largeMult _ = do
  xs <- SV.generateM @n $ \i ->
   deref <$> fieldInput Public ("x" <> show (toInteger i))
  fieldOutput "out" $ product xs

prop_largeMult :: Fr -> Property
prop_largeMult f = withMaxSuccess 1 $ 
  withSomeSNat n $ \(sn :: SNat n) -> 
    withKnownNat sn $
      let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (largeMult (Proxy @n))
          inputs = assignInputs bsVars $ 
            Map.fromList $ map (\i -> ("x" <> show i, fromInteger i + f)) [0 .. (fromIntegral n) - 1]
          w = solve bsVars bsCircuit inputs
          res = lookupVar bsVars "out" w
          expected = product inputs
      in res === Just expected
  where
    n :: Natural
    n = 100_000

--------------------------------------------------------------------------------

_fieldToBool :: Fr -> Bool
_fieldToBool x = x /= 0


boolToField_ :: Bool -> Fr
boolToField_ True = 1
boolToField_ False = 0