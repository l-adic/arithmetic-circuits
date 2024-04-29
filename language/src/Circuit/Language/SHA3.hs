{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | A straightforward, unoptimised <https://en.wikipedia.org/wiki/SHA-3 SHA3> implementation.
--
--    TODO: test on more than one block
module Circuit.Language.SHA3 where

import Circuit.Language
import Data.Bifunctor
import Data.Distributive (Distributive (distribute))
import Data.Field.Galois (GaloisField)
import Data.Finite (Finite)
import Data.List ((!!))
import Data.Maybe (fromJust)
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as V
import GHC.TypeNats (type (+))
import Lens.Micro
import Protolude

type BitVector f n = Vector n (Signal f Bool)

-- | Row major 5x5 matrix of 64 bit values
type SHA3State f = Vector 5 (Vector 5 (BitVector f 64))

xors :: BitVector f 64 -> BitVector f 64 -> BitVector f 64
xors = V.zipWith xor_

ands :: BitVector f 64 -> BitVector f 64 -> BitVector f 64
ands = V.zipWith and_

complement_ :: BitVector f 64 -> BitVector f 64
complement_ = V.map not_

-- | Theta block permutation step
theta :: forall f. SHA3State f -> SHA3State f
theta rows = distribute $ V.zipWith (map . xors) toXor $ distribute rows
  where
    paritys :: Vector 5 (BitVector f 64)
    paritys =
      let f :: Vector 5 (BitVector f 64) -> BitVector f 64
          f = V.foldl1 xors
       in map f (distribute rows)

    toXor :: Vector 5 (BitVector f 64)
    toXor =
      V.zipWith
        xors
        (rotateRight paritys (1 :: Finite 5))
        (map (flip rotateLeft (1 :: Finite 64)) $ rotateLeft paritys (1 :: Finite 5))

-- | Rho block permutation step
rho :: SHA3State f -> SHA3State f
rho s = V.zipWith (V.zipWith rotateLeft) s rots
  where
    rots :: Vector 5 (Vector 5 (Finite 64))
    rots =
      fromJust . V.fromList $
        map
          (fromJust . V.fromList)
          [ [ 0,
              1,
              62,
              28,
              27
            ],
            [ 36,
              44,
              6,
              55,
              20
            ],
            [ 3,
              10,
              43,
              25,
              39
            ],
            [ 41,
              45,
              15,
              21,
              8
            ],
            [ 18,
              2,
              61,
              56,
              14
            ]
          ]

-- | Pi block permutation step
pi_ :: SHA3State f -> SHA3State f
pi_ rows = fromJust $ V.fromList $ map (toList rows !!) order
  where
    order =
      [ 0,
        6,
        12,
        18,
        24,
        3,
        9,
        10,
        16,
        22,
        1,
        7,
        13,
        19,
        20,
        4,
        5,
        11,
        17,
        23,
        2,
        8,
        14,
        15,
        21
      ]

-- | Chi block permutation step
chi :: SHA3State f -> SHA3State f
chi rows = distribute $ V.zipWith3 (V.zipWith3 func) cols (rotateLeft cols (1 :: Finite 5)) (rotateLeft cols (2 :: Finite 5))
  where
    cols = distribute rows
    func :: BitVector f 64 -> BitVector f 64 -> BitVector f 64 -> BitVector f 64
    func x y z = x `xors` (complement_ y `ands` z)

-- | Iota block permutation step
iota ::
  forall f.
  (Num f) =>
  Finite 24 ->
  SHA3State f ->
  SHA3State f
iota i st = do
  let v = V.head st
      x = V.head v
      rest0 = V.tail v
      rest1 = V.tail st
   in ((x `xors` (consts ^. V.ix i)) `V.cons` rest0) `V.cons` rest1
  where
    -- TODO generate with LFSR
    consts :: Vector 24 (BitVector f 64)
    consts =
      let f :: Integer -> BitVector f 64
          f n = V.generate $ \_i ->
            if testBit n (fromIntegral _i)
              then cBool True
              else cBool False
       in map f $
            fromJust $
              V.fromList
                [ 0x0000000000000001,
                  0x0000000000008082,
                  0x800000000000808a,
                  0x8000000080008000,
                  0x000000000000808b,
                  0x0000000080000001,
                  0x8000000080008081,
                  0x8000000000008009,
                  0x000000000000008a,
                  0x0000000000000088,
                  0x0000000080008009,
                  0x000000008000000a,
                  0x000000008000808b,
                  0x800000000000008b,
                  0x8000000000008089,
                  0x8000000000008003,
                  0x8000000000008002,
                  0x8000000000000080,
                  0x000000000000800a,
                  0x800000008000000a,
                  0x8000000080008081,
                  0x8000000000008080,
                  0x0000000080000001,
                  0x8000000080008008
                ]

-- | Block permutation round
round :: (Num f) => Finite 24 -> SHA3State f -> SHA3State f
round i = iota i . chi . pi_ . rho . theta

-- | Xor the data to be hashed into the block
updateState :: ((n + n0) ~ 25, KnownNat n0) => Vector n (BitVector f 64) -> SHA3State f -> SHA3State f
updateState dat st =
  V.zipWith xors st (dat ++ replicate 0)

{-

-- | SHA3
sha3 ::
  forall dom n n0.
  (HiddenClockResetEnable dom, (n + n0) ~ 25, KnownNat n0) =>
  -- | Reset
  Signal dom Bool ->
  -- | Input block
  Signal dom (Vec n (BitVector 64)) ->
  -- | (Done, hash state)
  (Signal dom Bool, Signal dom SHA3State)
sha3 reset dat = (register False $ cnt .==. pure maxBound, state)
  where
    cnt :: Signal dom (Index 24)
    cnt = register 0 $ step <$> cnt <*> reset
      where
        step 0 False = 0
        step cnt _
          | cnt == maxBound = 0
          | otherwise = cnt + 1

    roundsIn :: Signal dom SHA3State
    roundsIn = mux (cnt .==. 0) (updateState <$> dat <*> state) state

    state :: Signal dom SHA3State
    state =
      register (repeat (repeat 0)) $
        round <$> cnt <*> roundsIn

sha3Packed ::
  forall inputSize outputSize rate dom drop.
  (HiddenClockResetEnable dom, 1600 ~ (outputSize + drop), 25 ~ (inputSize + rate), KnownNat rate, KnownNat outputSize) =>
  Signal dom Bool ->
  Signal dom (Vec inputSize (BitVector 64)) ->
  (Signal dom Bool, Signal dom (BitVector outputSize))
sha3Packed start dat = second (fmap $ revBV . truncateB . revBV . pack . map swapEndian . concat) $ sha3 start dat

sha3_224 = sha3Packed @18 @224

sha3_256 = sha3Packed @17 @256

sha3_384 = sha3Packed @13 @384

sha3_512 = sha3Packed @9 @512

-}
