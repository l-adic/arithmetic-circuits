module Main where

import Circom.CLI (defaultMain)
import Circuit
import Circuit.Language
import Protolude

main :: IO ()
main = defaultMain "factors" program

program :: ExprM BN128 (Var Wire BN128 'TBool)
program = do
  a <- var_ <$> fieldInput Private "a"
  b <- var_ <$> fieldInput Private "b"
  n <- var_ <$> fieldInput Public "n"
  k <- var_ <$> fieldInput Public "k"
  let kBits = split_ k
      kIsEven = boolToField (atIndex_ kBits 0) `eq_` cField 0
  zs <- map var_ <$> fieldInputs @5 Public "zs"
  let s = unAdd_ $ foldMap Add_ zs
      cs =
        [ neq_ n a,
          neq_ n b,
          eq_ n (a * b + s),
          kIsEven
        ]
  boolOutput "out" $ unAnd_ $ foldMap And_ cs
