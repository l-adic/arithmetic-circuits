{-# LANGUAGE NoImplicitPrelude #-}

-- To get the benchmarking data, run "stack bench".

module Main where

import Circuit.Bench qualified
import Criterion.Main
import Protolude

main :: IO ()
main =
  defaultMain
    [ Circuit.Bench.benchmarks
    ]
