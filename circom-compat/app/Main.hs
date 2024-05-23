module Main where

import Circom.CLI (defaultMain)
import Circuit
import Circuit.Language
import Data.Field.Galois (Prime)
import Protolude

main :: IO ()
main = defaultMain "factors" program

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

program :: ExprM Fr (Var Wire Fr 'TBool)
program = do
  a <- var_ <$> fieldInput Private "a"
  b <- var_ <$> fieldInput Private "b"
  n <- var_ <$> fieldInput Public "n"
  let cs =
        [ neq_ n a,
          neq_ n b,
          eq_ n (a * b)
        ]
  boolOutput "out" $ unAnd_ $ foldMap And_ cs
