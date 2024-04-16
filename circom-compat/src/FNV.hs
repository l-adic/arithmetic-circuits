module FNV
  ( fnv1a,
    hashText,
    FNVHash (..),
    mkFNV,
    fnvLSB,
    fnvMSB,
  )
where

import Data.ByteString qualified as B
import Data.Text.Encoding qualified as TE
import Protolude
import Text.PrettyPrint.Leijen.Text (Pretty (..), text)

--------------------------------------------------------------------------------
-- fnv
--------------------------------------------------------------------------------

newtype FNVHash = FNVHash Word64 deriving (Show, Eq, Ord)

instance Pretty FNVHash where
  pretty (FNVHash h) = text $ show h

-- FNV-1a constants for 64-bit hashing
initialState :: Word64
initialState = 0xcbf29ce484222325

fnvPrime :: Word64
fnvPrime = 0x100000001b3

-- Hash a list of Word8 using FNV-1a
fnv1a :: [Word8] -> FNVHash
fnv1a = FNVHash . foldl' fnv1aStep initialState
  where
    fnv1aStep acc byte = (acc `xor` fromIntegral byte) * fnvPrime

fnvLSB :: FNVHash -> Word32
fnvLSB (FNVHash h) = fromIntegral (h .&. 0xFFFFFFFF)

-- Function to extract the most significant 32 bits (MSB)
fnvMSB :: FNVHash -> Word32
fnvMSB (FNVHash h) = fromIntegral (h `shiftR` 32)

mkFNV :: Word32 -> Word32 -> FNVHash
mkFNV msb lsb = FNVHash $ fromIntegral msb `shiftL` 32 .|. fromIntegral lsb

hashText :: Text -> FNVHash
hashText = fnv1a . textToUtf8
  where
    textToUtf8 = B.unpack . TE.encodeUtf8
