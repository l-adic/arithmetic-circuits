module R1CS.Circom
  ( CircomR1CS (..),
    r1csToCircomR1CS,
    r1csFromCircomR1CS,
    Preamble (..),
    R1CSHeader (..),
    CircomWitness (..),
    WitnessHeader (..),
    witnessToCircomWitness,
    witnessFromCircomWitness,
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
import Data.Field.Galois (GaloisField (char), PrimeField, fromP)
import Data.Map qualified as Map
import Protolude
import R1CS (LinearPoly (..), R1C (..), R1CS (..), Witness (..))
import Prelude (fail)

--------------------------------------------------------------------------------
-- R1CS
--------------------------------------------------------------------------------

data CircomR1CS f = CircomR1CS
  { crPreamble :: Preamble,
    crHeader :: R1CSHeader,
    crConstraints :: [R1C f],
    crWireMap :: [Word64]
  }
  deriving (Show, Eq)

r1csToCircomR1CS :: forall f. (GaloisField f) => R1CS f -> CircomR1CS f
r1csToCircomR1CS R1CS {..} =
  CircomR1CS
    { crPreamble =
        Preamble
          { magic = 0x73633172,
            version = 1,
            nSections = 3
          },
      crHeader =
        R1CSHeader
          { rhFieldSize = FieldSize 32,
            rhPrime = fromIntegral $ char (1 :: f),
            rhNVars = fromIntegral r1csNumVars,
            rhNPubOut = fromIntegral r1csNumOutputs,
            rhNPubIn = fromIntegral r1csNumPublicInputs,
            rhNPrvIn = fromIntegral r1csNumPrivateInputs,
            -- I'm not sure what a label is, but i doubt we're using it
            rhNLabels = 0,
            rhNConstraints = fromIntegral $ length r1csConstraints
          },
      crConstraints = r1csConstraints,
      -- we make strong the assumption that variables are numbered from 0 to n-1
      crWireMap = [0 .. fromIntegral r1csNumVars - 1]
    }

r1csFromCircomR1CS :: CircomR1CS f -> R1CS f
r1csFromCircomR1CS (CircomR1CS {..}) =
  R1CS
    { r1csConstraints = crConstraints,
      r1csNumVars = fromIntegral $ rhNVars crHeader,
      r1csNumPublicInputs = fromIntegral $ rhNPubIn crHeader,
      r1csNumPrivateInputs = fromIntegral $ rhNPrvIn crHeader,
      r1csNumOutputs = fromIntegral $ rhNPubOut crHeader
    }

newtype CircomR1CSBuilder k = CircomR1CSBuilder (CircomR1CS k -> CircomR1CS k)

newtype FieldSize = FieldSize Int32 deriving (Show, Eq)

instance (PrimeField k) => Binary (CircomR1CS k) where
  get = do
    preamble <- getPreamble 0x73633172
    header <- lookAhead findHeader
    builders <- replicateM (fromIntegral $ nSections preamble) (parseR1CSSection header)
    let def =
          CircomR1CS
            { crPreamble = preamble,
              crHeader = header,
              crConstraints = [],
              crWireMap = []
            }
    pure $ foldr (\(CircomR1CSBuilder f) acc -> f acc) def builders
    where
      findHeader :: Get R1CSHeader
      findHeader = do
        sectionType <- getWord32le
        len <- getInt64le
        case sectionType of
          0x00000001 -> getR1CSHeader
          _ -> do
            skip $ fromIntegral len
            findHeader

  put CircomR1CS {..} = do
    putPreamble crPreamble
    putHeaderSection
    putConstraintsSection
    putWireMapSection
    where
      putHeaderSection = do
        putWord32le 0x00000001
        let bytes = runPut $ putcrHeader crHeader
        putWord64le (fromIntegral (LBS.length bytes))
        void $ putLazyByteString bytes
      putConstraintsSection = do
        putWord32le 0x00000002
        let bytes = runPut $ putConstraints (rhFieldSize crHeader) crConstraints
        putWord64le $ fromIntegral (LBS.length bytes)
        void $ putLazyByteString bytes
      putWireMapSection = do
        putWord32le 0x00000003
        let bytes = runPut $ putWireMap crWireMap
        putWord64le $ fromIntegral (LBS.length bytes)
        void $ putLazyByteString bytes

parseR1CSSection :: (PrimeField k) => R1CSHeader -> Get (CircomR1CSBuilder k)
parseR1CSSection header@(R1CSHeader {rhNConstraints, rhNVars, rhFieldSize}) = do
  sectionType <- getWord32le
  len <- getInt64le
  case sectionType of
    0x00000001 -> do
      skip $ fromIntegral len
      pure . CircomR1CSBuilder $ \rc1s -> rc1s {crHeader = header}
    0x00000002 -> do
      constraints <- getConstraints rhFieldSize (fromIntegral rhNConstraints)
      pure . CircomR1CSBuilder $ \rc1s -> rc1s {crConstraints = constraints}
    0x00000003 -> do
      wireMap <- getWireMap (fromIntegral rhNVars)
      pure . CircomR1CSBuilder $ \rc1s -> rc1s {crWireMap = wireMap}
    st -> fail $ "unexpected r1cs section type " <> show st

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

data Preamble = Preamble
  { magic :: Word32,
    version :: Word32,
    nSections :: Word32
  }
  deriving (Show, Eq)

getPreamble :: Word32 -> Get Preamble
getPreamble typeMagic = do
  magic <- getWord32le
  when (typeMagic /= magic)
    $ fail ("invalid magic number, expected " <> show typeMagic <> " but got " <> show magic)
  version <- getWord32le
  nSections <- getWord32le
  pure Preamble {..}

putPreamble :: Preamble -> Put
putPreamble Preamble {..} = do
  putWord32le magic
  putWord32le version
  putWord32le nSections

--------------------------------------------------------------------------------
-- Header
--------------------------------------------------------------------------------

data R1CSHeader = R1CSHeader
  { rhFieldSize :: FieldSize,
    rhPrime :: Integer,
    rhNVars :: Word32,
    rhNPubOut :: Word32,
    rhNPubIn :: Word32,
    rhNPrvIn :: Word32,
    rhNLabels :: Word64,
    rhNConstraints :: Word32
  }
  deriving (Show, Eq)

getR1CSHeader :: Get R1CSHeader
getR1CSHeader = do
  fieldSize <- getInt32le
  when (fieldSize /= 32) $ fail ("field size must be 32 bytes " <> show fieldSize)
  rhPrime <- integerFromLittleEndian <$> replicateM (fromIntegral fieldSize) getWord8
  rhNVars <- getWord32le
  rhNPubOut <- getWord32le
  rhNPubIn <- getWord32le
  rhNPrvIn <- getWord32le
  rhNLabels <- getWord64le
  rhNConstraints <- getWord32le
  pure
    $ R1CSHeader
      { rhFieldSize = FieldSize fieldSize,
        rhPrime,
        rhNVars,
        rhNPubOut,
        rhNPubIn,
        rhNPrvIn,
        rhNLabels,
        rhNConstraints
      }

putcrHeader :: R1CSHeader -> Put
putcrHeader R1CSHeader {rhFieldSize = fieldSize@(FieldSize fs), ..} = do
  putInt32le fs
  mapM_ putWord8 (integerToLittleEndian fieldSize rhPrime)
  putWord32le rhNVars
  putWord32le rhNPubOut
  putWord32le rhNPubIn
  putWord32le rhNPrvIn
  putWord64le rhNLabels
  putWord32le rhNConstraints

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
-- Witness
--------------------------------------------------------------------------------

data CircomWitness f = CircomWitness
  { wtnsPreamble :: Preamble,
    wtnsHeader :: WitnessHeader,
    wtnsValues :: [f]
  }
  deriving (Show, Eq)

witnessToCircomWitness :: forall f. (PrimeField f) => Witness f -> CircomWitness f
witnessToCircomWitness (Witness m) =
  CircomWitness
    { wtnsPreamble =
        Preamble
          { magic = 0x736e7477,
            version = 1,
            nSections = 2
          },
      wtnsHeader =
        WitnessHeader
          { whFieldSize = FieldSize 32,
            whPrime = fromIntegral $ char (1 :: f),
            whWitnessSize = fromIntegral $ Map.size m
          },
      wtnsValues = Map.elems m
    }

witnessFromCircomWitness :: CircomWitness f -> Witness f
witnessFromCircomWitness (CircomWitness {wtnsValues}) =
  Witness $ Map.fromList $ zip [0 ..] wtnsValues

instance (PrimeField k) => Binary (CircomWitness k) where
  get = do
    preamble <- getPreamble 0x736e7477
    header <- lookAhead findHeader
    builders <- replicateM (fromIntegral $ nSections preamble) (parseWitnessSection header)
    let def =
          CircomWitness
            { wtnsPreamble = preamble,
              wtnsHeader = header,
              wtnsValues = []
            }
    pure $ foldr (\(CircomWitnessBuilder f) acc -> f acc) def builders
    where
      findHeader :: Get WitnessHeader
      findHeader = do
        sectionType <- getWord32le
        len <- getInt64le
        case sectionType of
          0x00000001 -> getWitnessHeader
          _ -> do
            skip $ fromIntegral len
            findHeader
  put CircomWitness {..} = do
    putPreamble wtnsPreamble
    putHeaderSection
    putWitnessSection
    where
      putHeaderSection = do
        putWord32le 0x00000001
        let bytes = runPut $ putWitnessHeader wtnsHeader
        putWord64le (fromIntegral (LBS.length bytes))
        void $ putLazyByteString bytes
      putWitnessSection = do
        putWord32le 0x00000002
        let bytes = runPut $ putWitnessValues (whFieldSize wtnsHeader) wtnsValues
        putWord64le $ fromIntegral (LBS.length bytes)
        void $ putLazyByteString bytes

newtype CircomWitnessBuilder f = CircomWitnessBuilder (CircomWitness f -> CircomWitness f)

parseWitnessSection :: (PrimeField f) => WitnessHeader -> Get (CircomWitnessBuilder f)
parseWitnessSection header@(WitnessHeader {whFieldSize, whWitnessSize}) = do
  sectionType <- getWord32le
  len <- getInt64le
  case sectionType of
    0x00000001 -> do
      skip $ fromIntegral len
      pure . CircomWitnessBuilder $ \wtns -> wtns {wtnsHeader = header}
    0x00000002 -> do
      values <- getWitnessValues whFieldSize (fromIntegral whWitnessSize)
      pure . CircomWitnessBuilder $ \wtns -> wtns {wtnsValues = values}
    st -> fail $ "unexpected wtns section type " <> show st

data WitnessHeader = WitnessHeader
  { whFieldSize :: FieldSize,
    whPrime :: Integer,
    whWitnessSize :: Word32
  }
  deriving (Show, Eq)

getWitnessHeader :: Get WitnessHeader
getWitnessHeader = do
  fieldSize <- getInt32le
  when (fieldSize /= 32) $ fail ("field size must be 32 bytes " <> show fieldSize)
  whPrime <- integerFromLittleEndian <$> replicateM (fromIntegral fieldSize) getWord8
  whWitnessSize <- getWord32le
  pure
    $ WitnessHeader
      { whFieldSize = FieldSize fieldSize,
        whPrime,
        whWitnessSize
      }

putWitnessHeader :: WitnessHeader -> Put
putWitnessHeader WitnessHeader {whFieldSize = FieldSize fs, whPrime, whWitnessSize} = do
  putInt32le fs
  mapM_ putWord8 (integerToLittleEndian (FieldSize fs) whPrime)
  putWord32le whWitnessSize

getWitnessValues :: (PrimeField f) => FieldSize -> Int -> Get [f]
getWitnessValues (FieldSize fieldSize) n =
  replicateM n (fromInteger . integerFromLittleEndian <$> replicateM (fromIntegral fieldSize) getWord8)

putWitnessValues :: (PrimeField f) => FieldSize -> [f] -> Put
putWitnessValues fieldSize values = do
  mapM_ (mapM_ putWord8 . integerToLittleEndian fieldSize . fromP) values

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
