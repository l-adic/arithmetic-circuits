module Test.R1CS.Circom where

import Data.Binary (decode, decodeFileOrFail, encode)
import Data.Binary.Get (ByteOffset)
import Data.Field.Galois (Prime)
import FNV
import Protolude
import R1CS (validateWitness)
import R1CS.Circom
import Test.Hspec
import Test.QuickCheck
import Prelude (String)

prop_endianConversion :: NonNegative Integer -> Property
prop_endianConversion (NonNegative n) =
  let n' = integerToLittleEndian (FieldSize 32) n
   in integerFromLittleEndian n' === n

spec_parseMultiplier :: Spec
spec_parseMultiplier = do
  describe "Binary file parsing" $ do
    it "correctly parses r1cs values from a file" $ do
      result1 :: Either (ByteOffset, String) (CircomR1CS F_BN128) <- decodeFileOrFail "circom-compat/examples/multiplier/circuit.r1cs"
      result1 `shouldSatisfy` isRight
      let res1 :: CircomR1CS F_BN128
          res1 = fromRight (panic "impossible") result1
      let encodedR1CS = encode res1
      let res2 = decode encodedR1CS
      res2 `shouldBe` res1

    it "correctly parses witness values from a file" $ do
      result1 :: Either (ByteOffset, String) (CircomWitness F_BN128) <- decodeFileOrFail "circom-compat/examples/multiplier/witness.wtns"
      result1 `shouldSatisfy` isRight
      let res1 :: CircomWitness F_BN128
          res1 = fromRight (panic "impossible") result1
      let encodedR1CS = encode res1
      let res2 = decode encodedR1CS
      res2 `shouldBe` res1

    it "can correctly verify the witness against the r1cs" $ do
      er1cs :: Either (ByteOffset, String) (CircomR1CS F_BN128) <- decodeFileOrFail "circom-compat/examples/multiplier/circuit.r1cs"
      er1cs `shouldSatisfy` isRight
      let r1cs :: CircomR1CS F_BN128
          r1cs = fromRight (panic "impossible") er1cs
      ewtns :: Either (ByteOffset, String) (CircomWitness F_BN128) <- decodeFileOrFail "circom-compat/examples/multiplier/witness.wtns"
      ewtns `shouldSatisfy` isRight
      let wtns :: CircomWitness F_BN128
          wtns = fromRight (panic "impossible") ewtns
      validateWitness (witnessFromCircomWitness wtns) (r1csFromCircomR1CS r1cs) `shouldBe` Right ()

  describe "FNV Hashing" $ do
    let stringToWord8s :: String -> [Word8]
        stringToWord8s = map (fromIntegral . ord)
    it "Can compute fnv hash according to the rust spec" $ do
      fnv1a (stringToWord8s []) `shouldBe` FNVHash 0xcbf29ce484222325
      fnv1a (stringToWord8s "a") `shouldBe` FNVHash 0xaf63dc4c8601ec8c
      fnv1a (stringToWord8s "b") `shouldBe` FNVHash 0xaf63df4c8601f1a5
      fnv1a (stringToWord8s "feedfacedeadbeef") `shouldBe` FNVHash 0xcac54572bb1a6fc8
      fnv1a (stringToWord8s "http://www.isthe.com/chongo/bio.html") `shouldBe` FNVHash 0x8c7609b4a9f10907

type P_BN128 = 21888242871839275222246405745257275088548364400416034343698204186575808495617

type F_BN128 = Prime P_BN128
