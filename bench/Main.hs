{-# LANGUAGE NoImplicitPrelude #-}

-- To get the benchmarking data, run "stack bench".

module Main where

import Circuit qualified
import Criterion.Main
import Protolude

main :: IO ()
main =
  defaultMain
    [ bgroup "Circuit to QAP translation" Circuit.benchmarks
    ]
