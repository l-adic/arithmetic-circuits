{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoStarIsType #-}

module Test.Circuit.Lang where

import Circuit
import Circuit.Language
import Circuit.Language.SHA3
import Crypto.Hash as CH
import Data.ByteArray qualified as BA
import Data.ByteString qualified as BS
import Data.Field.Galois (Prime, PrimeField (fromP))
import Data.Finite (Finite)
import Data.Map qualified as Map
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as SV
import GHC.TypeNats (type (*), type (+))
import Protolude
import Test.QuickCheck (Arbitrary (..), Property, withMaxSuccess, (=/=), (===), (==>))
import Test.QuickCheck.Monadic (monadicIO, run)
import Prelude qualified

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

nBits :: Int
nBits = fromIntegral $ natVal (Proxy @(NBits Fr))

bitSplitJoin :: ExprM Fr (Var Wire Fr Fr)
bitSplitJoin = do
  _x <- deref <$> fieldInput Public "x"
  out <- VarField <$> freshPublicInput "out"
  ret out $ join_ $ split_ _x

prop_bitsSplitJoin :: Fr -> Property
prop_bitsSplitJoin x =
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
   in lookupVar bsVars "out" w === x

prop_bitsSplitJoinContra :: Fr -> Fr -> Property
prop_bitsSplitJoinContra x y =
  (x /= y) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bitSplitJoin
        input = assignInputs bsVars $ Map.singleton "x" x
        w = solve bsVars bsCircuit input
     in lookupVar bsVars "out" w =/= y

factors :: ExprM Fr (Var Wire Fr Fr)
factors = do
  n <- deref <$> fieldInput Public "n"
  a <- deref <$> fieldInput Public "a"
  b <- deref <$> fieldInput Public "b"
  let isFactorization = eq_ n (a * b)
  out <- VarBool <$> freshPublicInput "out"
  ret (boolToField out) (boolToField isFactorization)

prop_factorization :: Fr -> Fr -> Property
prop_factorization x y =
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder factors
      inputs = assignInputs bsVars $ Map.fromList [("n", x * y), ("a", x), ("b", y)]
      w = solve bsVars bsCircuit inputs
   in lookupVar bsVars "out" w === 1

prop_factorizationContra :: Fr -> Fr -> Fr -> Property
prop_factorizationContra x y z =
  (x * y /= z) ==>
    let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder factors
        inputs = assignInputs bsVars $ Map.fromList [("n", z), ("a", x), ("b", y)]
        w = solve bsVars bsCircuit inputs
     in lookupVar bsVars "out" w == 0

bitIndex :: Finite (NBits Fr) -> ExprM Fr (Var Wire Fr Fr)
bitIndex i = do
  x <- deref <$> fieldInput Public "x"
  let bits = split_ x
  bi <- atIndex i bits
  out <- VarBool <$> freshPublicInput "out"
  ret (boolToField out) (boolToField bi)

prop_bitIndex :: Int -> Fr -> Property
prop_bitIndex i x =
  let _i = i `mod` nBits
      _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (bitIndex $ fromIntegral _i)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
   in (lookupVar bsVars "out" w) === if testBit _x _i then 1 else 0

setAtIndex :: Finite (NBits Fr) -> Bool -> ExprM Fr (Var Wire Fr Fr)
setAtIndex i b = do
  x <- deref <$> fieldInput Public "x"
  let bits = split_ x
  bits' <- updateIndex_ i (cBool b) bits
  out <- VarField <$> freshPublicInput "out"
  ret out $ join_ bits'

prop_setAtIndex :: Int -> Fr -> Bool -> Property
prop_setAtIndex i x b =
  let _i = i `mod` nBits
      _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (setAtIndex (fromIntegral _i) b)
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
   in res === fromInteger (if b then setBit _x _i else clearBit _x _i)

-- TODO: investigate why this one is SCARY SLOW
bundleUnbundle :: ExprM Fr (Var Wire Fr Fr)
bundleUnbundle = do
  x <- deref <$> fieldInput Public "x"
  bits <- unbundle $ split_ x
  let negated = map not_ bits
  let res = unAdd_ $ foldMap (Add_ . coerceGroundType) negated
  out <- VarField <$> freshPublicInput "out"
  ret out res

prop_bundleUnbundle :: Fr -> Property
prop_bundleUnbundle x =
  let _x = fromP x
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder bundleUnbundle
      input = assignInputs bsVars $ Map.singleton "x" x
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = foldl (\acc i -> acc + if testBit _x i then 0 else 1) 0 [0 .. nBits - 1]
   in res === fromInteger expected

sharingProg :: ExprM Fr (Var Wire Fr Fr)
sharingProg = do
  x <- deref <$> fieldInput Public "x"
  y <- deref <$> fieldInput Public "y"
  let z = x * y
  out <- VarField <$> freshPublicInput "out"
  ret out $ sum $ replicate 10 z

prop_sharingProg :: Fr -> Fr -> Property
prop_sharingProg x y = monadicIO $ run $ do
  let _x = fromP x
      _y = fromP y
      BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder sharingProg
      input = assignInputs bsVars $ Map.fromList [("x", x), ("y", y)]
      w = solve bsVars bsCircuit input
      res = lookupVar bsVars "out" w
      expected = fromInteger $ sum $ replicate 10 (_x * _y)
  pure $ res === expected

sha3Program :: ExprM Fr (Vector 256 (Var Wire Fr Fr))
sha3Program = do
  bits <- fmap deref <$> boolsInput Public "b_"
  let res = sha3_256 $ chunk bits
  outs <- SV.generateM $ \i -> do
    let label = "out_" <> show i
    v <- VarBool <$> freshPublicInput label
    pure $ boolToField @(Var Wire Fr Bool) v
    
  retMany outs $ boolToField (bundle res)

--------------------------------------------------------------------------------

_fieldToBool :: Fr -> Bool
_fieldToBool x = x /= 0

lookupVar :: CircuitVars Text -> Text -> Map Int f -> f
lookupVar vs label sol = do
  let var = fromMaybe (panic $ "Missing label " <> label) $ Map.lookup label (cvInputsLabels vs)
  case Map.lookup var sol of
    Just v -> v
    Nothing -> panic $ "Variable not found: " <> show var

assignInputs :: CircuitVars Text -> Map Text f -> Map Int f
assignInputs CircuitVars {..} inputs =
  let res =
        Map.fromList
          [ (var, val)
            | (l1, var) <- Map.toList cvInputsLabels,
              (l2, val) <- Map.toList inputs,
              l1 == l2
          ]
   in res

unpack :: [Bool] -> Word8
unpack bools = foldl setBit zeroBits (map fst . filter snd $ indexedBools)
  where
    indexedBools = zip [0 .. 8] bools

chunkList :: Int -> [a] -> [[a]]
chunkList _ [] = []
chunkList n xs
  | n > 0 = take n xs : (chunkList n (drop n xs))
  | otherwise = panic "Chunk size must be greater than zero."

boolToField_ :: Bool -> Fr
boolToField_ True = 1
boolToField_ False = 0

--------------------------------------------------------------------------------

{-

BuilderState {bsVars = shaVars, bsCircuit = shaCircuit} = snd $ runCircuitBuilder sha3Program

prop :: forall n n0. (((n + 1) + n0) ~ 25, KnownNat n0, KnownNat ((n + 1) * 64)) => ([Word8] -> [Word8]) -> Int -> Vector n (Vector 64 Bool) -> Property
prop hashFunc mdlen vec = monadicIO $ run $ do
  let inputVec :: Vector ((n + 1) * 64) Bool
      inputVec = concatVec (vec `SV.snoc` mkBitVector @Integer 0x8000000000000006)
      inIndices :: [Finite ((n + 1) * 64)]
      inIndices = [minBound .. maxBound]
      assignments =
        Map.fromList $
          map (\i -> ("b_" <> show @Int (fromIntegral i), boolToField_ $ inputVec `SV.index` i)) inIndices
  let input =
        assignInputs shaVars $ assignments
  let w = altSolve shaCircuit input
  let outIndices :: [Finite 256]
      outIndices = [minBound .. maxBound]
      res :: [Bool]
      res = map (\i -> _fieldToBool $ lookupVar shaVars ("out_" <> show (fromIntegral @_ @Int i)) w) outIndices
  let str = reverse $ map unpack $ chunkList 8 $ toList inputVec
  let resStr = take mdlen $ mkOutput res
  let testIn = mkOutput $ toList inputVec
  let expect = hashFunc testIn
  pure $ resStr === expect

mkOutput :: [Bool] -> [Word8]
mkOutput = map unpack . chunkList 8

--
propsha256 :: ArbVec -> Property
propsha256 (ArbVec v) =
  withMaxSuccess 1 $
    prop (\x -> BA.unpack (CH.hash (BS.pack x) :: Digest SHA3_256)) 32 v

newtype ArbVec = ArbVec (Vector 16 (Vector 64 Bool)) deriving (Eq)

instance Show ArbVec where
  show (ArbVec v) = show $ mkOutput $ toList $ concatVec v

instance Arbitrary (ArbVec) where
  arbitrary = ArbVec <$> SV.replicateM (SV.replicateM arbitrary)

altSolve :: ArithCircuit Fr -> Map Int Fr -> Map Int Fr
altSolve program inputs =
  evalArithCircuit
    (\w m -> Map.lookup (wireName w) m)
    (\w m -> Map.insert (wireName w) m)
    program
    inputs
-}