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
import Data.Maybe (fromJust)
import Data.Vector qualified as V
import Data.Vector.Sized qualified as SV
import Protolude
import Test.QuickCheck (Arbitrary (arbitrary), Property, forAll, vectorOf, (.&&.), (=/=), (===), (==>))

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
   in lookupVar bsVars "out" w === Just x .&&. computed === V.singleton x

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
   in lookupVar bsVars "out" w === Just 1 .&&. computed === V.singleton 1

prop_factorizationContra :: Fr -> Fr -> Fr -> Property
prop_factorizationContra x y z =
  (x * y /= z) ==>
    let (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder factors
        inputs = assignInputs bsVars $ Map.fromList [("n", z), ("a", x), ("b", y)]
        w = solve bsVars bsCircuit inputs
        computed = evalExpr IntMap.lookup inputs (relabelExpr wireName prog)
     in lookupVar bsVars "out" w == Just 0 .&&. computed == V.singleton 0

bitIndex :: Finite (NBits Fr) -> ExprM Fr (Expr Wire Fr 'TBool)
bitIndex i = do
  x <- var_ <$> fieldInput Public "x"
  let bits = split_ x
  let bi = atIndex_ bits i
  void $ boolOutput "out" bi
  pure bi

prop_bitIndex :: Int -> Fr -> Property
prop_bitIndex i x =
  let _i = i `mod` nBits
      _x = fromP x
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (bitIndex $ fromIntegral _i)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      expected = if testBit _x _i then 1 else 0
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in lookupVar bsVars "out" w === Just expected .&&. computed === V.singleton expected

setAtIndex :: Finite (NBits Fr) -> Bool -> ExprM Fr (Expr Wire Fr 'TField)
setAtIndex i b = do
  x <- var_ <$> fieldInput Public "x"
  let bits = split_ x
      bits' = updateAtIndex_ bits i (cBool b)
      res = join_ bits'
  void $ fieldOutput "out" res
  pure res

prop_setAtIndex :: Int -> Fr -> Bool -> Property
prop_setAtIndex i x b =
  let _i = i `mod` nBits
      _x = fromP x
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (setAtIndex (fromIntegral _i) b)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = fromInteger (if b then setBit _x _i else clearBit _x _i)
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in res === Just expected .&&. computed === V.singleton expected

-- TODO: investigate why this one is SCARY SLOW
bundleUnbundle :: ExprM Fr (Expr Wire Fr 'TField)
bundleUnbundle = do
  x <- var_ <$> fieldInput Public "x"
  let bits = unbundle_ $ split_ x
  let negated = map not_ bits
  let res = unAdd_ $ foldMap (Add_ . boolToField) negated
  void $ fieldOutput "out" res
  pure res

prop_bundleUnbundle :: Fr -> Property
prop_bundleUnbundle x =
  let _x = fromP x
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder bundleUnbundle
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = foldl (\acc i -> acc + if testBit _x i then 0 else 1) 0 [0 .. nBits - 1]
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in res === Just expected .&&. computed === V.singleton expected

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
   in res === Just expected .&&. computed === V.singleton expected

--------------------------------------------------------------------------------

boolBinopsProg ::
  BinOp Fr ('TVec 50 'TBool) ->
  ExprM Fr (Expr Wire Fr ('TVec 50 'TBool))
boolBinopsProg op = do
  xs <- SV.generateM $ \i ->
    var_ <$> boolInput Public ("x" <> showFinite i)
  ys <- SV.generateM $ \i ->
    var_ <$> boolInput Public ("y" <> showFinite i)
  zs <- SV.generateM $ \i ->
    VarBool <$> freshOutput ("out" <> showFinite i)
  let res = binOp_ op (bundle_ xs) (bundle_ ys)
  void $ boolsOutput zs $ binOp_ op (bundle_ xs) (bundle_ ys)
  pure res

propBoolBinopsProg ::
  BinOp Fr ('TVec 50 'TBool) ->
  (Bool -> Bool -> Bool) ->
  Property
propBoolBinopsProg top op = forAll arbInputs $ \(bs, bs') ->
  let _xs = zip (map (\i -> "x" <> show @Int i) [0 ..]) bs
      _ys = zip (map (\i -> "y" <> show @Int i) [0 ..]) bs'
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (boolBinopsProg top)
      input =
        assignInputs bsVars $
          fmap boolToField $
            Map.fromList (_xs <> _ys)
      w = solve bsVars bsCircuit input
      expected = map boolToField $ zipWith op bs bs'
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in ( all (\(i, b) -> lookupVar bsVars ("out" <> show @Int i) w == Just b) $
          zip [0 ..] expected
      )
        .&&. computed === (V.fromList expected)
  where
    arbInputs = ((,) <$> vectorOf 50 arbitrary <*> vectorOf 50 arbitrary)

prop_andsProg :: Property
prop_andsProg = propBoolBinopsProg BAnds (&&)

prop_orsProg :: Property
prop_orsProg = propBoolBinopsProg BOrs (||)

prop_xorsProg :: Property
prop_xorsProg = propBoolBinopsProg BXors (/=)

--------------------------------------------------------------------------------

fieldBinopsProg :: BinOp Fr (TVec 50 'TField) -> ExprM Fr (Expr Wire Fr ('TVec 50 'TField))
fieldBinopsProg op = do
  xs <- SV.generateM $ \i ->
    var_ <$> fieldInput Public ("x" <> showFinite i)
  ys <- SV.generateM $ \i ->
    var_ <$> fieldInput Public ("y" <> showFinite i)
  zs <- SV.generateM $ \i ->
    VarField <$> freshOutput ("out" <> showFinite i)
  let res = binOp_ op (bundle_ xs) (bundle_ ys)
  void $ fieldsOutput zs res
  pure res

propFieldBinopsProg ::
  (BinOp Fr ('TVec 50 'TField)) ->
  (Fr -> Fr -> Fr) ->
  Property
propFieldBinopsProg top op = forAll arbInputs $ \(bs, bs') ->
  let _xs = zip (map (\i -> "x" <> show @Int i) [0 ..]) bs
      _ys = zip (map (\i -> "y" <> show @Int i) [0 ..]) bs'
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (fieldBinopsProg top)
      input =
        assignInputs bsVars $
          Map.fromList (_xs <> _ys)
      w = solve bsVars bsCircuit input
      expected = zipWith op bs bs'
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in ( all (\(i, b) -> lookupVar bsVars ("out" <> show @Int i) w == Just b) $
          zip [0 ..] expected
      )
        .&&. computed === V.fromList expected
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
  UnOp Fr ('TVec 32 'TBool) ->
  ExprM Fr (Expr Wire Fr ('TVec 32 'TBool))
boolUnopsProg op = do
  xs <- SV.generateM $ \i ->
    var_ <$> boolInput Public ("x" <> showFinite i)
  zs <- SV.generateM $ \i ->
    VarBool <$> freshOutput ("out" <> showFinite i)
  let res = unOp_ op (bundle_ xs)
  void $ boolsOutput zs res
  pure res

propBitVecUnopsProg ::
  UnOp Fr ('TVec 32 'TBool) ->
  ([Bool] -> [Bool]) ->
  Property
propBitVecUnopsProg top op = forAll arbInputs $ \bs ->
  let _xs = zip (map (\i -> "x" <> show @Int i) [0 ..]) bs
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (boolUnopsProg top)
      input = assignInputs bsVars $ fmap boolToField $ Map.fromList _xs
      w = solve bsVars bsCircuit input
      expected = op bs
      a = intToBitVec $ bitOp $ bitVecToInt bs
      out = fromJust $ sequence $ map (\i -> lookupVar bsVars ("out" <> show @Int i) w) [0 .. 31]
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in map boolToField expected === out .&&. map _fieldToBool out === a .&&. computed === V.fromList (map boolToField expected)
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
  UnOp Fr ('TVec 50 'TField) ->
  ExprM Fr (Expr Wire Fr ('TVec 50 'TField))
fieldUnopsProg op = do
  xs <- SV.generateM $ \i ->
    var_ <$> fieldInput Public ("x" <> showFinite i)
  zs <- SV.generateM $ \i ->
    VarField <$> freshOutput ("out" <> showFinite i)
  let res = unOp_ op (bundle_ xs)
  void $ fieldsOutput zs res
  pure res

propFieldUnopsProg ::
  UnOp Fr ('TVec 50 'TField) ->
  (Fr -> Fr) ->
  Property
propFieldUnopsProg top op = forAll arbInputs $ \bs ->
  let _xs = zip (map (\i -> "x" <> show @Int i) [0 ..]) bs
      (prog, BuilderState {bsVars, bsCircuit}) = runCircuitBuilder (fieldUnopsProg top)
      input =
        assignInputs bsVars $
          Map.fromList _xs
      w = solve bsVars bsCircuit input
      expected = map op bs
      computed = evalExpr IntMap.lookup input (relabelExpr wireName prog)
   in ( all (\(i, b) -> lookupVar bsVars ("out" <> show @Int i) w == Just b) $
          zip [0 ..] expected
      )
        .&&. computed == V.fromList expected
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

_fieldToBool :: Fr -> Bool
_fieldToBool x = x /= 0
