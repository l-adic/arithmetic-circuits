module R1CS.Circom
  ( CircomR1CS (..),
    Preamble (..),
    Header (..),
    FieldSize (..),
    -- for testing
    integerFromLittleEndian,
    integerToLittleEndian,
  )
where

import Data.Binary (Binary (..), Get, Put, getWord8, putWord8)
import Data.Binary.Get (getInt32le, getInt64le, getWord32le, getWord64le, lookAhead, skip)
import Data.Binary.Put (putInt32le, putLazyByteString, putWord32le, putWord64le, runPut)
import Data.ByteString.Lazy qualified as LBS
import Data.Field.Galois (PrimeField, fromP)
import Data.Map qualified as Map
import Protolude
import R1CS (LinearPoly (..), R1C (..))
import Prelude (fail)

--------------------------------------------------------------------------------
-- R1CS
--------------------------------------------------------------------------------

data CircomR1CS f = CircomR1CS
  { r1csPreamble :: Preamble,
    r1csHeader :: Header,
    r1csConstraints :: [R1C f],
    r1csWireMap :: [Word64]
  }
  deriving (Show)

deriving instance (Eq k) => Eq (CircomR1CS k)

newtype CircomR1CSBuilder k = CircomR1CSBuilder (CircomR1CS k -> CircomR1CS k)

newtype FieldSize = FieldSize Int32 deriving (Show, Eq)

instance (PrimeField k) => Binary (CircomR1CS k) where
  get = do
    preamble <- getPreamble
    header <- lookAhead findHeader
    builders <- replicateM (fromIntegral $ nSections preamble) (parseSection header)
    let def =
          CircomR1CS
            { r1csPreamble = preamble,
              r1csHeader = header,
              r1csConstraints = [],
              r1csWireMap = []
            }
    pure $ foldr (\(CircomR1CSBuilder f) acc -> f acc) def builders
    where
      findHeader :: Get Header
      findHeader = do
        sectionType <- getWord32le
        len <- getInt64le
        case sectionType of
          0x00000001 -> getHeader
          _ -> do
            skip $ fromIntegral len
            findHeader

  put CircomR1CS {..} = do
    putPreamble r1csPreamble
    putHeaderSection
    putConstraintsSection
    putWireMapSection
    where
      putHeaderSection = do
        putWord32le 0x00000001
        let bytes = runPut $ putHeader r1csHeader
        putWord64le (fromIntegral (LBS.length bytes))
        void $ putLazyByteString bytes
      putConstraintsSection = do
        putWord32le 0x00000002
        let bytes = runPut $ putConstraints (fieldSize r1csHeader) r1csConstraints
        putWord64le $ fromIntegral (LBS.length bytes)
        void $ putLazyByteString bytes
      putWireMapSection = do
        putWord32le 0x00000003
        let bytes = runPut $ putWireMap r1csWireMap
        putWord64le $ fromIntegral (LBS.length bytes)
        void $ putLazyByteString bytes

parseSection :: (PrimeField k) => Header -> Get (CircomR1CSBuilder k)
parseSection header@(Header {nConstraints, nWires, fieldSize}) = do
  sectionType <- getWord32le
  len <- getInt64le
  case sectionType of
    0x00000001 -> do
      skip $ fromIntegral len
      pure . CircomR1CSBuilder $ \rc1s -> rc1s {r1csHeader = header}
    0x00000002 -> do
      constraints <- getConstraints fieldSize (fromIntegral nConstraints)
      pure . CircomR1CSBuilder $ \rc1s -> rc1s {r1csConstraints = constraints}
    0x00000003 -> do
      wireMap <- getWireMap (fromIntegral nWires)
      pure . CircomR1CSBuilder $ \rc1s -> rc1s {r1csWireMap = wireMap}
    st -> fail $ "unexpected section type " <> show st

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

data Preamble = Preamble
  { magicR1CS :: Word32,
    version :: Word32,
    nSections :: Word32
  }
  deriving (Show, Eq)

getPreamble :: Get Preamble
getPreamble = do
  magicR1CS <- getWord32le
  when (magicR1CS /= 0x73633172) $ fail "invalid magic number"
  version <- getWord32le
  nSections <- getWord32le
  pure Preamble {..}

putPreamble :: Preamble -> Put
putPreamble Preamble {..} = do
  putWord32le magicR1CS
  putWord32le version
  putWord32le nSections

--------------------------------------------------------------------------------
-- Header
--------------------------------------------------------------------------------

data Header = Header
  { fieldSize :: FieldSize,
    primeSize :: Integer,
    nWires :: Word32,
    nPubOut :: Word32,
    nPubIn :: Word32,
    nPrvIn :: Word32,
    nLabels :: Word64,
    nConstraints :: Word32
  }
  deriving (Show, Eq)

getHeader :: Get Header
getHeader = do
  fieldSize <- getInt32le
  when (fieldSize /= 32) $ fail ("field size must be 32 bytes " <> show fieldSize)
  primeSize <- integerFromLittleEndian <$> replicateM (fromIntegral fieldSize) getWord8
  nWires <- getWord32le
  nPubOut <- getWord32le
  nPubIn <- getWord32le
  nPrvIn <- getWord32le
  nLabels <- getWord64le
  nConstraints <- getWord32le
  pure
    $ Header
      { fieldSize = FieldSize fieldSize,
        primeSize,
        nWires,
        nPubOut,
        nPubIn,
        nPrvIn,
        nLabels,
        nConstraints
      }

putHeader :: Header -> Put
putHeader Header {fieldSize = fieldSize@(FieldSize fs), ..} = do
  putInt32le fs
  mapM_ putWord8 (integerToLittleEndian fieldSize primeSize)
  putWord32le nWires
  putWord32le nPubOut
  putWord32le nPubIn
  putWord32le nPrvIn
  putWord64le nLabels
  putWord32le nConstraints

--------------------------------------------------------------------------------
-- Constraints
--------------------------------------------------------------------------------

data Factor f = Factor
  { wireId :: Word32,
    value :: f
  }

getFactor :: (PrimeField k) => FieldSize -> Get (Factor k)
getFactor (FieldSize fieldSize) = do
  wireId <- getWord32le
  value <- fromInteger . integerFromLittleEndian <$> replicateM (fromIntegral fieldSize) getWord8
  pure $ Factor {..}

putFactor :: (PrimeField k) => FieldSize -> Factor k -> Put
putFactor fieldSize (Factor {..}) = do
  putWord32le wireId
  mapM_ putWord8 (integerToLittleEndian fieldSize (fromP value))

newtype LinearCombination k = LinearCombination [Factor k]

getLinearCombination :: (PrimeField f) => FieldSize -> Get (LinearCombination f)
getLinearCombination fieldSize = do
  nFactors <- getWord32le
  factors <- replicateM (fromIntegral nFactors) (getFactor fieldSize)
  pure $ LinearCombination factors

putLinearCombination :: (PrimeField f) => FieldSize -> LinearCombination f -> Put
putLinearCombination fieldSize (LinearCombination factors) = do
  putWord32le (fromIntegral (length factors))
  mapM_ (putFactor fieldSize) factors

getPoly :: (PrimeField f) => FieldSize -> Get (LinearPoly f)
getPoly fieldSize = do
  LinearCombination factors <- getLinearCombination fieldSize
  pure
    $ LinearPoly
    $ foldl (\acc (Factor {wireId, value}) -> Map.insert (fromIntegral wireId) value acc) mempty factors

putPoly :: (PrimeField k) => FieldSize -> LinearPoly k -> Put
putPoly fieldSize (LinearPoly p) =
  putLinearCombination fieldSize (LinearCombination [Factor {wireId = fromIntegral var, value} | (var, value) <- Map.toList p])

getR1C :: (PrimeField f) => FieldSize -> Get (R1C f)
getR1C fieldSize = do
  a <- getPoly fieldSize
  b <- getPoly fieldSize
  c <- getPoly fieldSize
  pure $ R1C (a, b, c)

putR1C :: (PrimeField k) => FieldSize -> R1C k -> Put
putR1C fieldSize (R1C (a, b, c)) = do
  putPoly fieldSize a
  putPoly fieldSize b
  putPoly fieldSize c

getConstraints :: (PrimeField f) => FieldSize -> Int -> Get [R1C f]
getConstraints fieldSize n = replicateM n (getR1C fieldSize)

putConstraints :: (PrimeField k) => FieldSize -> [R1C k] -> Put
putConstraints fieldSize = mapM_ (putR1C fieldSize)

--------------------------------------------------------------------------------
-- WireMap
--------------------------------------------------------------------------------

getWireMap :: Int -> Get [Word64]
getWireMap n = replicateM n getWord64le

putWireMap :: [Word64] -> Put
putWireMap = mapM_ putWord64le

--------------------------------------------------------------------------------

integerFromLittleEndian :: [Word8] -> Integer
integerFromLittleEndian bytes =
  foldl' (\acc (i, byte) -> acc .|. (fromIntegral byte `shiftL` (i * 8))) 0 (zip [0 ..] bytes)

integerToLittleEndian :: FieldSize -> Integer -> [Word8]
integerToLittleEndian (FieldSize fieldSize) n =
  let res = go n
      padLen = fromIntegral fieldSize - length res
   in res <> replicate padLen 0
  where
    go 0 = []
    go x = fromIntegral (x .&. 0xff) : go (x `shiftR` 8)
