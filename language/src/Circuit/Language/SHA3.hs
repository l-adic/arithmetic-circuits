{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE  NoStarIsType #-}
-- | A straightforward, unoptimised <https://en.wikipedia.org/wiki/SHA-3 SHA3> implementation.
--
--    TODO: test on more than one block
module Circuit.Language.SHA3 where

import Circuit.Language
import Data.Distributive (Distributive (distribute))
import Data.Finite (Finite)
import Data.Maybe (fromJust)
import Data.Vector.Sized (BuildVector (..), Vector, pattern Build)
import Data.Vector.Sized qualified as SV
import Data.Vector qualified as V
import GHC.TypeNats (type (+),  type (*))
import Lens.Micro
import Protolude
import Data.Field.Galois (GaloisField)



-- | Row major 5x5 matrix of 64 bit values
type SHA3State f = Vector 5 (Vector 5 (BitVector f 64))

emptyState :: forall f. Num f => SHA3State f
emptyState = SV.replicate (SV.replicate zeroBits_)

type BitVector f n = Vector n (Signal f Bool)

zeroBits_ :: Num f => BitVector f 64
zeroBits_ = SV.replicate (cBool False)

xors :: (Eq f, Num f) => BitVector f 64 -> BitVector f 64 -> BitVector f 64
xors = SV.zipWith xor_

ands :: (Eq f, Num f) => BitVector f 64 -> BitVector f 64 -> BitVector f 64
ands = SV.zipWith and_

complement_ :: (Num f) => BitVector f 64 -> BitVector f 64
complement_ = SV.map not_

--------------------------------------------------------------------------------

-- | Theta block permutation step
theta :: forall f. GaloisField f => SHA3State f -> SHA3State f
theta rows = trace @Text "theta" $ distribute $ SV.zipWith (map . xors) toXor $ distribute rows
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
rho = trace @Text "rho" $ chunk . SV.zipWith (flip rotateLeft) rots . concatVec
  where
    rots :: Vector 25 (Finite 64)
    rots =
      Build
        ( 0 :< 1 :< 62 :< 28 :< 27 :<
          36 :< 44 :< 6 :< 55 :< 20 :<
          3 :< 10 :< 43 :< 25 :< 39 :<
          41 :< 45 :< 15 :< 21 :< 8 :<
          18 :< 2 :< 61 :< 56 :< 14 :<
          Nil
        )

-- | Pi block permutation step
pi_ :: SHA3State f -> SHA3State f
pi_ rows = trace @Text "pi" $
  let as = concatVec rows
   in chunk $ map (\i -> as ^. SV.ix i) order
  where
    order :: Vector 25 (Finite 25)
    order =
        Build (0 :< 6 :< 12 :< 18 :< 24
        :< 3 :< 9 :< 10 :< 16 :< 22
        :< 1 :< 7 :< 13 :< 19 :< 20
        :< 4 :< 5 :< 11 :< 17 :< 23
        :< 2 :< 8 :< 14 :< 15 :< 21
        :< Nil)

-- | Chi block permutation step
chi :: forall f. GaloisField f => SHA3State f -> SHA3State f
chi rows = trace @Text "chi" $ distribute $ 
    SV.zipWith3 (SV.zipWith3 func) cols (rotateLeft cols (1 :: Finite 5)) (rotateLeft cols (2 :: Finite 5))
  where
    cols = distribute rows
    func :: BitVector f 64 -> BitVector f 64 -> BitVector f 64 -> BitVector f 64
    func x y z = x `xors` (complement_ y `ands` z)

mkBitVector :: forall a. Bits a => a -> Vector 64 Bool
mkBitVector a = SV.generate $ \_i -> 
  testBit a (fromIntegral _i)

 -- | Iota block permutation step
iota ::
  forall f.
  (GaloisField f) =>
  Finite 24 ->
  SHA3State f ->
  SHA3State f
iota i rows = trace @Text"iota" $ do
  let row1 = SV.head rows
      x = SV.head row1
      rest0 = SV.tail row1
      rest1 = SV.tail rows
   in (x `xors` (consts ^. SV.ix i)) `SV.cons` rest0 `SV.cons` rest1
  where
    consts :: Vector 24 (BitVector f 64)
    consts = map (map cBool . mkBitVector @Integer) $
           Build (0x0000000000000001 :<
                  0x0000000000008082 :<
                  0x800000000000808a :<
                  0x8000000080008000 :<
                  0x000000000000808b :<
                  0x0000000080000001 :<
                  0x8000000080008081 :<
                  0x8000000000008009 :<
                  0x000000000000008a :<
                  0x0000000000000088 :<
                  0x0000000080008009 :<
                  0x000000008000000a :<
                  0x000000008000808b :<
                  0x800000000000008b :<
                  0x8000000000008089 :<
                  0x8000000000008003 :<
                  0x8000000000008002 :<
                  0x8000000000000080 :<
                  0x000000000000800a :<
                  0x800000008000000a :<
                  0x8000000080008081 :<
                  0x8000000000008080 :<
                  0x0000000080000001 :<
                  0x8000000080008008 :< Nil
                )


-- | Block permutation round
round_ :: (GaloisField f) => Finite 24 -> SHA3State f -> SHA3State f
round_ i = 
  trace @Text "round_" $
    iota i . chi . pi_ . rho . theta

rounds :: Vector 1 (Finite 24)
rounds = fromJust $ SV.fromList [0]


keccakF :: forall f. GaloisField f => SHA3State f -> SHA3State f
keccakF st = SV.foldl (flip round_) st rounds


{-

absorbBlock :: Int -> V.Vector Word64 -> V.Vector Word64 -> V.Vector Word64
absorbBlock !rate !state !input
    | V.null input = state
    | otherwise    = absorbBlock rate (keccakF state') (V.drop (div rate 64) input)
    -- TODO this can be optimized with some sort of in-place manipulation
    where state' = V.imap (\z el -> if div z 5 + 5 * mod z 5 < threshold
                                    then el `xor` (input ! (div z 5 + 5 * mod z 5))
                                    else el) state
          threshold = div rate laneWidth


-}


-- | Xor the data to be hashed into the block
updateState ::  forall n n0 f.
  ((n + n0) ~ 25) => 
  GaloisField f =>
  KnownNat n0 => 
  Vector n (BitVector f 64) -> 
  SHA3State f -> 
  SHA3State f
updateState dat st = trace @Text "updateState" $
  chunk $ SV.zipWith xors (concatVec st) (dat SV.++ SV.replicate zeroBits_)

-- | SHA3
sha3 :: forall f n n0. 
  GaloisField f =>
  (n + n0) ~ 25 => 
  KnownNat n0 =>
  Vector n (BitVector f 64) ->
  SHA3State f
sha3 dat = trace @Text "sha3" $
  foldl (\st i -> round_ i (updateState dat st)) emptyState rounds


{-
len_bytes = md_size / 8. So for 256 it's 32
num_words = rate / 64 

-}


sha3Packed ::
  forall inputSize outputSize rate drop f.
  GaloisField f =>
  1600 ~ (outputSize + drop) => 
  25 ~ (inputSize + rate) =>
  KnownNat rate => 
  KnownNat outputSize =>
  Vector inputSize (BitVector f 64) ->
  BitVector f outputSize
sha3Packed dat = trace @Text "sha3Packed" $
  SV.reverse . SV.take . SV.reverse . concatVec . map (swapEndian @8) . concatVec $ sha3 dat

sha3_224 = sha3Packed @18 @224

sha3_256 = sha3Packed @17 @256

sha3_384 = sha3Packed @13 @384

sha3_512 = sha3Packed @9 @512

swapEndian 
    :: forall n f. KnownNat n
    => BitVector f (8 * n)
    -> BitVector f (8 * n)
swapEndian = trace @Text "swapEndian" $
  concatVec . SV.reverse . chunk @8

revBV :: forall n f. BitVector f n -> BitVector f  n
revBV = SV.reverse

concatVec :: forall n m a. Vector n (Vector m a) -> Vector (n * m) a
concatVec = SV.concatMap identity


chunk :: forall n m a. KnownNat n => KnownNat m => Vector (n * m) a -> Vector n (Vector m a)
chunk v =
  let v' = SV.fromSized v
  in  SV.generate @n $ \i ->
        let start = fromIntegral i * fromIntegral (natVal (Proxy @n))
            s = V.slice start (fromIntegral (natVal $ Proxy @m)) v'
       in case SV.toSized @m s of
            Just x -> x
            Nothing -> panic ("chunk: impossible " <> show (start) <> show (length s) )
