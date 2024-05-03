{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | A straightforward, unoptimised <https://en.wikipedia.org/wiki/SHA-3 SHA3> implementation.
--
--    TODO: test on more than one block
module Test.Circuit.SHA3 where

import Circuit.Language
import Data.Distributive (Distributive (distribute))
import Data.Finite (Finite)
import Data.Maybe (fromJust)
import Data.Vector qualified as V
import Data.Vector.Sized (BuildVector (..), Vector, pattern Build)
import Data.Vector.Sized qualified as SV
import GHC.TypeNats (type (*), type (+))
import Lens.Micro
import Protolude

-- import Crypto.Hash as CH
-- import Data.ByteArray qualified as BA
-- import Data.Vector.Sized (Vector)
-- import Data.Vector.Sized qualified as SV
-- import GHC.TypeNats (type (*), type (+))
-- import Protolude
-- import Test.QuickCheck (Arbitrary (..), Property, withMaxSuccess, (=/=), (===), (==>), Large (Large))
-- import Test.QuickCheck.Monadic (monadicIO, run)
-- import Prelude qualified
-- import GHC.TypeNats (Natural, withKnownNat, SNat, withSomeSNat)
-- import Data.ByteString qualified as BS

-- | Row major 5x5 matrix of 64 bit values
type SHA3State f = Vector 5 (Vector 5 (BitVector f 64))

emptyState :: forall f. (Hashable f) => (Num f) => SHA3State f
emptyState = SV.replicate (SV.replicate zeroBits_)

type BitVector f n = Vector n (Signal f Bool)

zeroBits_ :: (Hashable f) => (Num f) => BitVector f 64
zeroBits_ = SV.replicate (cBool False)

xors :: (Hashable f) => BitVector f 64 -> BitVector f 64 -> BitVector f 64
xors = SV.zipWith xor_

ands :: (Hashable f) => BitVector f 64 -> BitVector f 64 -> BitVector f 64
ands = SV.zipWith and_

complement_ :: (Hashable f) => BitVector f 64 -> BitVector f 64
complement_ = SV.map not_

--------------------------------------------------------------------------------

-- | Theta block permutation step
theta :: forall f. (Hashable f) => SHA3State f -> SHA3State f
theta rows = distribute $ SV.zipWith (map . xors) toXor $ distribute rows
  where
    paritys :: Vector 5 (BitVector f 64)
    paritys = map (SV.foldl1 xors) (distribute rows)

    toXor :: Vector 5 (BitVector f 64)
    toXor =
      SV.zipWith
        xors
        (rotateRight paritys (1 :: Finite 5))
        (map (flip rotateLeft (1 :: Finite 64)) $ rotateLeft paritys (1 :: Finite 5))

-- | Rho block permutation step
rho :: SHA3State f -> SHA3State f
rho = chunk . SV.zipWith (flip rotateLeft) rots . concatVec
  where
    rots :: Vector 25 (Finite 64)
    rots =
      Build
        ( 0
            :< 1
            :< 62
            :< 28
            :< 27
            :< 36
            :< 44
            :< 6
            :< 55
            :< 20
            :< 3
            :< 10
            :< 43
            :< 25
            :< 39
            :< 41
            :< 45
            :< 15
            :< 21
            :< 8
            :< 18
            :< 2
            :< 61
            :< 56
            :< 14
            :< Nil
        )

-- | Pi block permutation step
pi_ :: SHA3State f -> SHA3State f
pi_ rows =
  let as = concatVec rows
   in chunk $ map (\i -> as ^. SV.ix i) order
  where
    order :: Vector 25 (Finite 25)
    order =
      Build
        ( 0
            :< 6
            :< 12
            :< 18
            :< 24
            :< 3
            :< 9
            :< 10
            :< 16
            :< 22
            :< 1
            :< 7
            :< 13
            :< 19
            :< 20
            :< 4
            :< 5
            :< 11
            :< 17
            :< 23
            :< 2
            :< 8
            :< 14
            :< 15
            :< 21
            :< Nil
        )

-- | Chi block permutation step
chi :: forall f. (Hashable f) => SHA3State f -> SHA3State f
chi rows =
  distribute $
    SV.zipWith3 (SV.zipWith3 func) cols (rotateLeft cols (1 :: Finite 5)) (rotateLeft cols (2 :: Finite 5))
  where
    cols = distribute rows
    func :: BitVector f 64 -> BitVector f 64 -> BitVector f 64 -> BitVector f 64
    func x y z = x `xors` (complement_ y `ands` z)

mkBitVector :: forall a. (Bits a) => a -> Vector 64 Bool
mkBitVector a = SV.generate $ \_i ->
  testBit a (fromIntegral _i)

-- \| Iota block permutation step
iota ::
  forall f.
  (Hashable f, Num f) =>
  Finite 24 ->
  SHA3State f ->
  SHA3State f
iota i rows =
  let row1 = SV.head rows
      x = SV.head row1
      rest0 = SV.tail row1
      rest1 = SV.tail rows
   in (x `xors` (consts ^. SV.ix i)) `SV.cons` rest0 `SV.cons` rest1
  where
    consts :: Vector 24 (BitVector f 64)
    consts =
      map (map cBool . mkBitVector @Integer) $
        Build
          ( 0x0000000000000001
              :< 0x0000000000008082
              :< 0x800000000000808a
              :< 0x8000000080008000
              :< 0x000000000000808b
              :< 0x0000000080000001
              :< 0x8000000080008081
              :< 0x8000000000008009
              :< 0x000000000000008a
              :< 0x0000000000000088
              :< 0x0000000080008009
              :< 0x000000008000000a
              :< 0x000000008000808b
              :< 0x800000000000008b
              :< 0x8000000000008089
              :< 0x8000000000008003
              :< 0x8000000000008002
              :< 0x8000000000000080
              :< 0x000000000000800a
              :< 0x800000008000000a
              :< 0x8000000080008081
              :< 0x8000000000008080
              :< 0x0000000080000001
              :< 0x8000000080008008
              :< Nil
          )

-- | Block permutation round
round_ :: (Hashable f, Num f) => Finite 24 -> SHA3State f -> SHA3State f
round_ i = iota i . chi . pi_ . rho . theta

rounds :: Vector 4 (Finite 24)
rounds = fromJust $ SV.fromList [0 .. 3]

-- | Xor the data to be hashed into the block
updateState ::
  forall n n0 f.
  ((n + n0) ~ 25) =>
  (Hashable f) =>
  (Num f) =>
  (KnownNat n0) =>
  Vector n (BitVector f 64) ->
  SHA3State f ->
  SHA3State f
updateState dat st =
  chunk $ SV.zipWith xors (concatVec st) (dat SV.++ SV.replicate zeroBits_)

-- | SHA3
sha3 ::
  forall f n n0.
  (Hashable f) =>
  (Num f) =>
  ((n + n0) ~ 25) =>
  (KnownNat n0) =>
  Vector n (BitVector f 64) ->
  SHA3State f
sha3 dat =
  foldl (\st i -> round_ i (updateState dat st)) emptyState rounds

{-
len_bytes = md_size / 8. So for 256 it's 32
num_words = rate / 64

-}

sha3Packed ::
  forall inputSize outputSize rate drop f.
  (Hashable f) =>
  (Num f) =>
  (1600 ~ (outputSize + drop)) =>
  (25 ~ (inputSize + rate)) =>
  (KnownNat rate) =>
  (KnownNat outputSize) =>
  Vector inputSize (BitVector f 64) ->
  BitVector f outputSize
sha3Packed dat =
  SV.reverse . SV.take . SV.reverse . concatVec . map (swapEndian @8) . concatVec $ sha3 dat

sha3_224 = sha3Packed @18 @224

sha3_256 = sha3Packed @17 @256

sha3_384 = sha3Packed @13 @384

sha3_512 = sha3Packed @9 @512

swapEndian ::
  forall n f.
  (KnownNat n) =>
  BitVector f (8 * n) ->
  BitVector f (8 * n)
swapEndian = concatVec . SV.reverse . chunk @8

revBV :: forall n f. BitVector f n -> BitVector f n
revBV = SV.reverse

concatVec :: forall n m a. Vector n (Vector m a) -> Vector (n * m) a
concatVec = SV.concatMap identity

chunk :: forall n m a. (KnownNat n) => (KnownNat m) => Vector (n * m) a -> Vector n (Vector m a)
chunk v =
  let v' = SV.fromSized v
   in SV.generate @n $ \i ->
        let start = fromIntegral i * fromIntegral (natVal (Proxy @n))
            s = V.slice start (fromIntegral (natVal $ Proxy @m)) v'
         in case SV.toSized @m s of
              Just x -> x
              Nothing -> panic ("chunk: impossible " <> show (start) <> show (length s))

--------------------------------------------------------------------------------

{-

sha3Program :: ExprM Fr (Vector 256 (Var Wire Fr Fr))
sha3Program = do
  bits <- fmap deref <$> boolsInput Public "b_"
  let res = sha3_256 $ chunk bits
  outs <- SV.generateM $ \i -> do
    let label = "out_" <> show i
    v <- VarBool <$> freshPublicInput label
    pure $ boolToField @(Var Wire Fr Bool) v

  retMany outs $ boolToField (bundle res)

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

unpack :: [Bool] -> Word8
unpack bools = foldl setBit zeroBits (map fst . filter snd $ indexedBools)
  where
    indexedBools = zip [0 .. 8] bools

chunkList :: Int -> [a] -> [[a]]
chunkList _ [] = []
chunkList n xs
  | n > 0 = take n xs : (chunkList n (drop n xs))
  | otherwise = panic "Chunk size must be greater than zero."
-}