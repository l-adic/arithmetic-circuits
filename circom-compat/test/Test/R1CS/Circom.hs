{-# LANGUAGE DataKinds #-}

module Test.R1CS.Circom where

import Data.Binary (decode, decodeFileOrFail, encode)
import Data.Binary.Get (ByteOffset)
import Data.Field.Galois (Prime)
import Protolude
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

type P_BN128 = 21888242871839275222246405745257275088548364400416034343698204186575808495617

type F_BN128 = Prime P_BN128
