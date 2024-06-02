{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoStarIsType #-}

module Test.Circuit.Lang where

import Circuit
import Circuit.Language
import Data.Field.Galois (PrimeField (fromP))
import Data.Finite (Finite)
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Data.Vector qualified as V
import Protolude
import Test.QuickCheck (Arbitrary (arbitrary), Property, forAll, vectorOf, (.&&.), (=/=), (===), (==>))

nBits :: Int
nBits = fromIntegral $ natVal (Proxy @(NBits BN128))

bitSplitJoin :: ExprM BN128 (Expr Wire BN128 'TField)
bitSplitJoin = do
  _x <- var_ <$> fieldInput Public "x"
  let res = join_ $ split_ _x
  void $ fieldOutput "out" $ res
  pure res

prop_bitsSplitJoin :: BN128 -> Property
prop_bitsSplitJoin x =
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder bitSplitJoin
      input = assignInputs bsVars $ Map.singleton "x" (Simple x)
      w = solve bsVars bsCircuit input
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupVar bsVars "out" w === Just x .&&. computed === Right (V.singleton x)

prop_bitsSplitJoinContra :: BN128 -> BN128 -> Property
prop_bitsSplitJoinContra x y =
  (x /= y) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
        input = assignInputs bsVars $ Map.singleton "x" (Simple x)
        w = solve bsVars bsCircuit input
     in lookupVar bsVars "out" w =/= Just y

factors :: ExprM BN128 (Expr Wire BN128 'TBool)
factors = do
  n <- var_ <$> fieldInput Public "n"
  a <- var_ <$> fieldInput Public "a"
  b <- var_ <$> fieldInput Public "b"
  let isFactorization = eq_ n (a * b)
  void $ boolOutput "out" isFactorization
  pure isFactorization

prop_factorization :: BN128 -> BN128 -> Property
prop_factorization x y =
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder factors
      inputs = assignInputs bsVars $ Map.fromList [("n", Simple $ x * y), ("a", Simple x), ("b", Simple y)]
      w = solve bsVars bsCircuit inputs
      computed = evalExpr IntMap.lookup inputs (relabelExpr wireName prog)
   in lookupVar bsVars "out" w === Just 1 .&&. computed === Right (V.singleton 1)

prop_factorizationContra :: BN128 -> BN128 -> BN128 -> Property
prop_factorizationContra x y z =
  (x * y /= z) ==>
    let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder factors
        inputs = assignInputs bsVars $ Map.fromList [("n", Simple z), ("a", Simple x), ("b", Simple y)]
        w = solve bsVars bsCircuit inputs
        computed = evalExpr IntMap.lookup inputs (relabelExpr wireName prog)
     in lookupVar bsVars "out" w == Just 0 .&&. computed == Right (V.singleton 0)

bitIndex :: Finite (NBits BN128) -> ExprM BN128 (Expr Wire BN128 'TBool)
bitIndex i = do
  x <- var_ <$> fieldInput Public "x"
  let bits = split_ x
  let bi = atIndex_ bits i
  void $ boolOutput "out" bi
  pure bi

prop_bitIndex :: Int -> BN128 -> Property
prop_bitIndex i x =
  let _i = i `mod` nBits
      _x = fromP x
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (bitIndex $ fromIntegral _i)
      input = assignInputs bsVars $ Map.singleton "x" (Simple x)
      w = solve bsVars bsCircuit input
      expected = if testBit _x _i then 1 else 0
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupVar bsVars "out" w === Just expected .&&. computed === Right (V.singleton expected)

setAtIndex :: Finite (NBits BN128) -> Bool -> ExprM BN128 (Expr Wire BN128 'TField)
setAtIndex i b = do
  x <- var_ <$> fieldInput Public "x"
  let bits = split_ x
      bits' = updateAtIndex_ bits i (cBool b)
      res = join_ bits'
  void $ fieldOutput "out" res
  pure res

prop_setAtIndex :: Int -> BN128 -> Bool -> Property
prop_setAtIndex i x b =
  let _i = i `mod` nBits
      _x = fromP x
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (setAtIndex (fromIntegral _i) b)
      input = assignInputs bsVars $ Map.singleton "x" (Simple x)
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = fromInteger (if b then setBit _x _i else clearBit _x _i)
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in res === Just expected .&&. computed === Right (V.singleton expected)

-- TODO: investigate why this one is SCARY SLOW
bundleUnbundle :: ExprM BN128 (Expr Wire BN128 'TField)
bundleUnbundle = do
  x <- var_ <$> fieldInput Public "x"
  let bits = unbundle_ $ split_ x
  let negated = map not_ bits
  let res = unAdd_ $ foldMap (Add_ . boolToField) negated
  void $ fieldOutput "out" res
  pure res

prop_bundleUnbundle :: BN128 -> Property
prop_bundleUnbundle x =
  let _x = fromP x
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder bundleUnbundle
      input = assignInputs bsVars $ Map.singleton "x" (Simple x)
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = foldl (\acc i -> acc + if testBit _x i then 0 else 1) 0 [0 .. nBits - 1]
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in res === Just expected .&&. computed === Right (V.singleton expected)

sharingProg :: ExprM BN128 (Expr Wire BN128 'TField)
sharingProg = do
  x <- var_ <$> fieldInput Public "x"
  y <- var_ <$> fieldInput Public "y"
  let z = sum $ replicate 10 (x * y)
  void $ fieldOutput "out" z
  pure $ z

prop_sharingProg :: BN128 -> BN128 -> Property
prop_sharingProg x y =
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (sharingProg)
      input = assignInputs bsVars $ Map.fromList [("x", Simple x), ("y", Simple y)]
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = sum $ replicate 10 (x * y)
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in res === Just expected .&&. computed === Right (V.singleton expected)

--------------------------------------------------------------------------------

boolBinopsProg ::
  BinOp BN128 ('TVec 50 'TBool) ->
  ExprM BN128 (Expr Wire BN128 ('TVec 50 'TBool))
boolBinopsProg op = do
  xs <- map var_ <$> boolInputs Public "x"
  ys <- map var_ <$> boolInputs Public "y"
  let res = binOp_ op (bundle_ xs) (bundle_ ys)
  void $ boolOutputs "out" $ binOp_ op (bundle_ xs) (bundle_ ys)
  pure res

propBoolBinopsProg ::
  BinOp BN128 ('TVec 50 'TBool) ->
  (Bool -> Bool -> Bool) ->
  Property
propBoolBinopsProg top op = forAll arbInputs $ \(bs, bs') ->
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (boolBinopsProg top)
      input =
        assignInputs bsVars $
          Map.fromList
            [ ("x", Array (map boolToField bs)),
              ("y", Array (map boolToField bs'))
            ]
      w = solve bsVars bsCircuit input
      expected = map boolToField $ zipWith op bs bs'
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupArrayVars bsVars "out" w === Just expected
        .&&. computed === Right (V.fromList expected)
  where
    arbInputs = ((,) <$> vectorOf 50 arbitrary <*> vectorOf 50 arbitrary)

prop_andsProg :: Property
prop_andsProg = propBoolBinopsProg BAnds (&&)

prop_orsProg :: Property
prop_orsProg = propBoolBinopsProg BOrs (||)

prop_xorsProg :: Property
prop_xorsProg = propBoolBinopsProg BXors (/=)

--------------------------------------------------------------------------------

fieldBinopsProg :: BinOp BN128 (TVec 50 'TField) -> ExprM BN128 (Expr Wire BN128 ('TVec 50 'TField))
fieldBinopsProg op = do
  xs <- map var_ <$> fieldInputs Public "x"
  ys <- map var_ <$> fieldInputs Public "y"
  let res = binOp_ op (bundle_ xs) (bundle_ ys)
  void $ fieldOutputs "out" res
  pure res

propFieldBinopsProg ::
  (BinOp BN128 ('TVec 50 'TField)) ->
  (BN128 -> BN128 -> BN128) ->
  Property
propFieldBinopsProg top op = forAll arbInputs $ \(bs, bs') ->
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (fieldBinopsProg top)
      input = assignInputs bsVars $ Map.fromList [("x", Array bs), ("y", Array bs')]
      w = solve bsVars bsCircuit input
      expected = zipWith op bs bs'
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupArrayVars bsVars "out" w == Just expected
        .&&. computed === Right (V.fromList expected)
  where
    arbInputs = ((,) <$> vectorOf 50 arbitrary <*> vectorOf 50 arbitrary)

prop_addsProg :: Property
prop_addsProg = propFieldBinopsProg BAdds (+)

prop_subsProg :: Property
prop_subsProg = propFieldBinopsProg BSubs (-)

prop_mulsProg :: Property
prop_mulsProg = propFieldBinopsProg BMuls (*)

prop_divsProg :: Property
prop_divsProg = propFieldBinopsProg BDivs (/)

--------------------------------------------------------------------------------

boolUnopsProg ::
  UnOp BN128 ('TVec 32 'TBool) ->
  ExprM BN128 (Expr Wire BN128 ('TVec 32 'TBool))
boolUnopsProg op = do
  xs <- map var_ <$> boolInputs @32 Public "x"
  let res = unOp_ op (bundle_ xs)
  void $ boolOutputs "out" res
  pure res

propBitVecUnopsProg ::
  UnOp BN128 ('TVec 32 'TBool) ->
  ([Bool] -> [Bool]) ->
  Property
propBitVecUnopsProg top op = forAll arbInputs $ \bs ->
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (boolUnopsProg top)
      input =
        assignInputs bsVars $
          Map.singleton "x" (Array $ map boolToField bs)
      w = solve bsVars bsCircuit input
      expected = op bs
      a = intToBitVec $ bitOp $ bitVecToInt bs
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupArrayVars bsVars "out" w == Just (map boolToField expected)
        .&&. computed === Right (V.fromList (map boolToField expected))
        .&&. expected === a
  where
    arbInputs = vectorOf 32 arbitrary
    bitOp = case top of
      URot n -> flip rotate n
      UNots -> complement
      UShift n -> flip shift n
      UReverse -> bitVecToInt . reverse . intToBitVec

prop_notsProg :: Property
prop_notsProg = propBitVecUnopsProg UNots (map not)

prop_rotateProg :: Int -> Property
prop_rotateProg n = propBitVecUnopsProg (URot n) (rotateList n)

prop_shiftProg :: Int -> Property
prop_shiftProg n = abs n <= 32 ==> propBitVecUnopsProg (UShift n) (shiftList False n)

--------------------------------------------------------------------------------

fieldUnopsProg ::
  UnOp BN128 ('TVec 50 'TField) ->
  ExprM BN128 (Expr Wire BN128 ('TVec 50 'TField))
fieldUnopsProg op = do
  xs <- map var_ <$> fieldInputs @50 Public "x"
  let res = unOp_ op (bundle_ xs)
  void $ fieldOutputs "out" res
  pure res

propFieldUnopsProg ::
  UnOp BN128 ('TVec 50 'TField) ->
  (BN128 -> BN128) ->
  Property
propFieldUnopsProg top op = forAll arbInputs $ \bs ->
  let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (fieldUnopsProg top)
      input = assignInputs bsVars $ Map.singleton "x" (Array bs)
      w = solve bsVars bsCircuit input
      expected = map op bs
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupArrayVars bsVars "out" w == Just expected
        .&&. computed == Right (V.fromList expected)
  where
    arbInputs = vectorOf 50 arbitrary

prop_negs :: Property
prop_negs = propFieldUnopsProg UNegs Protolude.negate

--------------------------------------------------------------------------------

showFinite :: (KnownNat n) => Finite n -> Text
showFinite = show . toInteger

intToBitVec :: Word32 -> [Bool]
intToBitVec n = map (testBit n) [0 .. 31]

bitVecToInt :: [Bool] -> Word32
bitVecToInt bs = foldl (\acc (b, i) -> if b then setBit acc i else acc) zeroBits (zip bs [0 ..])

prop_bitVecIntInverse :: Word32 -> Property
prop_bitVecIntInverse n = bitVecToInt (intToBitVec n) === n

prop_intBitVecInverse :: Property
prop_intBitVecInverse = forAll (vectorOf 32 arbitrary) $ \bs ->
  intToBitVec (bitVecToInt bs) === bs

_fieldToBool :: BN128 -> Bool
_fieldToBool x = x /= 0
