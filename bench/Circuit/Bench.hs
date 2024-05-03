{-# LANGUAGE DataKinds #-}

module Circuit.Bench where

import Circuit
import Circuit.Language
import Criterion
import Data.Field.Galois (Prime)
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Data.Vector (generateM)
import GHC.TypeNats (Natural, SNat, withKnownNat, withSomeSNat)
import Protolude

type Fr = Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617

benchmarks :: Benchmark
benchmarks =
  bgroup
    "largeMult"
    [ bench "1_000" $ whnf largeMult 1000,
      bench "10_000" $ whnf largeMult 10000,
      bench "100_000" $ whnf largeMult 100_000,
      bench "1_000_000" $ whnf largeMult 1_000_000
    ]

largeMult :: Natural -> Fr
largeMult n =
  withSomeSNat n $ \(sn :: SNat n) ->
    withKnownNat sn $
      let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (program (Proxy @n))
          inputs =
            assignInputs bsVars $
              Map.fromList $
                map (\i -> (nameInput i, fromIntegral i + 1)) [0 .. n - 1]
          w = altSolve bsCircuit inputs
       in fromMaybe (panic "output not found") $ lookupVar bsVars "out" w

nameInput :: (Integral a) => a -> Text
nameInput i = "x" <> show (toInteger i)

program :: forall n. (KnownNat n) => Proxy n -> ExprM Fr (Var Wire Fr Fr)
program p = do
  xs <- generateM (fromIntegral $ natVal p) $ \i ->
    var_ <$> fieldInput Public (nameInput i)
  fieldOutput "out" $ product xs

altSolve :: ArithCircuit Fr -> IntMap Fr -> IntMap Fr
altSolve p inputs =
  evalArithCircuit
    (\w m -> IntMap.lookup (wireName w) m)
    (\w m -> IntMap.insert (wireName w) m)
    p
    inputs
