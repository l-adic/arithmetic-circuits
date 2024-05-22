module Main where

import Circom.CLI (defaultMain)
import Circom.R1CS (r1csToCircomR1CS)
import Circom.Solver (CircomProgram (..), mkCircomProgram, nativeGenWitness)
import Circuit
import Circuit.Language
import Data.Binary (decodeFile, encodeFile)
import Data.Field.Galois (Prime)
import Data.Map qualified as Map
import Protolude
import R1CS (toR1CS)

main :: IO ()
main = defaultMain "factors" program

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

program :: ExprM Fr (Var Wire Fr 'TBool)
program = do
  n <- var_ <$> fieldInput Public "n"
  a <- var_ <$> fieldInput Private "a"
  b <- var_ <$> fieldInput Private "b"
  boolOutput "out" $ eq_ n (a * b)
