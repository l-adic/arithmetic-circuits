{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | A straightforward, unoptimised <https://en.wikipedia.org/wiki/SHA-3 SHA3> implementation.
--
--    TODO: test on more than one block
module Test.Circuit.SHA3 where

import Circuit
import Circuit.Language
import Crypto.Hash as CH
import Data.ByteArray qualified as BA
import Data.ByteString qualified as BS
import Data.Distributive (Distributive (distribute))
import Data.Field.Galois (GaloisField, Prime)
import Data.Finite (Finite)
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Data.Vector qualified as V
import Data.Vector.Sized (BuildVector (..), Vector, pattern Build)
import Data.Vector.Sized qualified as SV
import GHC.TypeNats (type (*), type (+))
import Lens.Micro
import Protolude
import Test.QuickCheck (Arbitrary (..), Property, withMaxSuccess, (===))
import Test.QuickCheck.Monadic (monadicIO, run)
import Prelude qualified

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

type BitVector f n = Signal f ('TVec n 'TBool)

-- | Row major 5x5 matrix of 64 bit values
type SHA3State f = Vector 5 (Vector 5 (BitVector f 64))

emptyState :: forall f. (Hashable f) => (GaloisField f) => SHA3State f
emptyState = SV.replicate (SV.replicate zeroBits_)

xors :: (Hashable f) => BitVector f 64 -> BitVector f 64 -> BitVector f 64
xors = xors_

ands :: (Hashable f) => BitVector f 64 -> BitVector f 64 -> BitVector f 64
ands = ands_

complement_ :: (Hashable f) => BitVector f 64 -> BitVector f 64
complement_ = nots_

--------------------------------------------------------------------------------

-- | Theta block permutation step
theta :: forall f. (Hashable f, GaloisField f) => SHA3State f -> SHA3State f
theta rows = distribute $ SV.zipWith (map . xors) toXor $ distribute rows
  where
    paritys :: Vector 5 (BitVector f 64)
    paritys = map (SV.foldl1 xors) (distribute rows)

    toXor :: Vector 5 (BitVector f 64)
    toXor =
      SV.zipWith
        xors
        (rotateRight @Int paritys 1)
        (map (flip rotateL 1) $ rotateLeft @Int paritys 1)

-- | Rho block permutation step
rho :: (GaloisField f) => (Hashable f) => SHA3State f -> SHA3State f
rho = chunk . SV.zipWith (flip rotateL) rots . concatVec
  where
    rots :: Vector 25 Int
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
    SV.zipWith3 (SV.zipWith3 func) cols (rotateLeft @Int cols 1) (rotateLeft @Int cols 2)
  where
    cols = distribute rows
    func :: BitVector f 64 -> BitVector f 64 -> BitVector f 64 -> BitVector f 64
    func x y z = x `xors` (complement_ y `ands` z)

mkBitVector :: forall a f. (Hashable f) => (GaloisField f) => (Bits a) => a -> BitVector f 64
mkBitVector = bundle_ . map cBool . mkBitVector'

mkBitVector' :: forall a. (Bits a) => a -> Vector 64 Bool
mkBitVector' a = SV.generate $ \_i -> testBit a (fromIntegral _i)

-- \| Iota block permutation step
iota ::
  forall f.
  (Hashable f, GaloisField f) =>
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
      map (mkBitVector @Integer) $
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
round_ :: (Hashable f, GaloisField f) => Finite 24 -> SHA3State f -> SHA3State f
round_ i = iota i . chi . pi_ . rho . theta

-- | Xor the data to be hashed into the block
updateState ::
  forall n n0 f.
  ((n + n0) ~ 25) =>
  (Hashable f) =>
  (GaloisField f) =>
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
  (GaloisField f) =>
  ((n + n0) ~ 25) =>
  (KnownNat n0) =>
  Vector n (BitVector f 64) ->
  SHA3State f
sha3 dat =
  foldl (\st i -> round_ i (updateState dat st)) emptyState rounds
  where
    rounds :: Vector 4 (Finite 24)
    rounds = fromJust $ SV.fromList [0 .. 3]

{-
len_bytes = md_size / 8. So for 256 it's 32
num_words = rate / 64

-}

sha3Packed ::
  forall inputSize outputSize rate drop f.
  (Hashable f) =>
  (GaloisField f) =>
  (1600 ~ (outputSize + drop)) =>
  (25 ~ (inputSize + rate)) =>
  (KnownNat rate) =>
  (KnownNat outputSize) =>
  -- Unbundled f (Vector 25 (BitVector f 64)) ~ Vector 25 (Vector 64 (Signal f TBool)) =>
  Vector inputSize (BitVector f 64) ->
  BitVector f outputSize
sha3Packed dat =
  let bs :: Vector 25 (Vector 64 (Signal f 'TBool))
      bs = map unbundle_ $ concatVec $ sha3 dat
      ds = truncate_ $ bundle_ $ SV.reverse $ concatVec $ map (swapEndian @8) bs
   in reverse_ ds
  where
    swapEndian ::
      forall n.
      (KnownNat n) =>
      Vector (8 * n) (Signal f 'TBool) ->
      Vector (8 * n) (Signal f 'TBool)
    swapEndian = concatVec . SV.reverse . chunk @8

concatVec :: forall n m a. Vector n (Vector m a) -> Vector (n * m) a
concatVec = SV.concatMap identity

sha3_224 = sha3Packed @18 @224

sha3_256 = sha3Packed @17 @256

sha3_384 = sha3Packed @13 @384

sha3_512 = sha3Packed @9 @512

chunk :: forall n m a. (KnownNat n) => (KnownNat m) => Vector (n * m) a -> Vector n (Vector m a)
chunk v =
  let v' = SV.fromSized v
   in SV.generate @n $ \i ->
        let start = fromIntegral i * fromIntegral (natVal (Proxy @n))
            s = V.slice start (fromIntegral (natVal $ Proxy @m)) v'
         in case SV.toSized @m s of
              Just x -> x
              Nothing -> panic ("chunk: impossible " <> show (start) <> show (length s))

rotateLeft ::
  (Enum i, KnownNat n) =>
  SV.Vector n a ->
  i ->
  SV.Vector n a
rotateLeft xs i = map ((\idx -> xs ^. SV.ix idx) . (\idx -> fromIntegral $ idx `mod` len)) (fromJust $ SV.fromList $ take len $ iterate (+ 1) i')
  where
    i' = fromEnum i
    len = length xs
{-# INLINE rotateLeft #-}

rotateRight ::
  (Enum i, KnownNat n) =>
  SV.Vector n a ->
  i ->
  SV.Vector n a
rotateRight xs i = map ((\idx -> xs ^. SV.ix idx) . (\idx -> fromIntegral $ idx `mod` len)) (fromJust $ SV.fromList $ take len $ iterate (+ 1) i')
  where
    i' = negate (fromEnum i)
    len = length xs
{-# INLINE rotateRight #-}

--------------------------------------------------------------------------------

sha3Program :: (KnownNat n) => Proxy n -> ExprM Fr (Vector 256 (Var Wire Fr 'TBool))
sha3Program _ = do
  bits :: Vector n (Signal f 'TBool) <- SV.generateM $ \i ->
    var_ <$> boolInput Public ("b_" <> show (toInteger i))
  let res = sha3_256 $ map bundle_ $ chunk bits
  outs <- SV.generateM $ \i -> do
    let label = "out_" <> show (toInteger i)
    VarBool <$> freshPublicInput label
  boolsOutput outs res

prop :: forall n n0. (((n + 1) + n0) ~ 25, KnownNat n0, KnownNat ((n + 1) * 64)) => ([Word8] -> [Word8]) -> Int -> Vector n (Vector 64 Bool) -> Property
prop hashFunc mdlen vec = withMaxSuccess 1 $ monadicIO $ run $ do
  let BuilderState {bsVars = shaVars, bsCircuit = shaCircuit} = snd $ runCircuitBuilder $ sha3Program (Proxy :: Proxy ((n + 1) * 64))
      inputVec = vec `SV.snoc` mkBitVector' @Integer 0x8000000000000006
      inIndices :: [Finite ((n + 1) * 64)]
      inIndices = [minBound .. maxBound]
      assignments =
        Map.fromList $
          map (\i -> ("b_" <> show @Int (fromIntegral i), boolToField_ $ concatVec inputVec `SV.index` i)) inIndices
  let input =
        assignInputs shaVars $
          assignments
  let w = altSolve shaCircuit input
  let outIndices :: [Finite 256]
      outIndices = [minBound .. maxBound]
      res :: [Bool]
      res = map (\i -> _fieldToBool $ fromJust $ lookupVar shaVars ("out_" <> show (fromIntegral @_ @Int i)) w) outIndices
  -- let str = reverse $ map unpack $ chunkList 8 $ toList inputVec
  let resStr = take mdlen $ mkOutput res
  let testIn = mkOutput $ toList (concatVec inputVec)
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

altSolve :: ArithCircuit Fr -> IntMap Fr -> IntMap Fr
altSolve program inputs =
  evalArithCircuit
    (\w m -> IntMap.lookup (wireName w) m)
    (\w m -> IntMap.insert (wireName w) m)
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

_fieldToBool :: Fr -> Bool
_fieldToBool x = x /= 0

boolToField_ :: Bool -> Fr
boolToField_ True = 1
boolToField_ False = 0
