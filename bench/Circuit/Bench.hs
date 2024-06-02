module Circuit.Bench where

import Circuit
import Circuit.Language
import Criterion
import Data.IntMap qualified as IntMap
import Data.Map qualified as Map
import Protolude

benchmarks :: Benchmark
benchmarks =
  bgroup
    "largeMult"
    [ bench "1_000" $ whnf largeMult (Proxy @1000),
      bench "10_000" $ whnf largeMult (Proxy @10000),
      bench "100_000" $ whnf largeMult (Proxy @100_000),
      bench "1_000_000" $ whnf largeMult (Proxy @1_000_000)
    ]

largeMult :: (KnownNat n) => Proxy n -> IO BN128
largeMult n =
  let BuilderState {bsVars, bsCircuit} = snd $ runCircuitBuilder (program n)
      inputs =
        assignInputs bsVars $ Map.singleton "x" (Array $ map fromIntegral [1 .. natVal n])
      w = altSolve bsCircuit inputs
      res = fromMaybe (panic "output not found") $ lookupVar bsVars "out" w
   in pure res

program :: forall n. (KnownNat n) => Proxy n -> ExprM BN128 (Var Wire BN128 'TField)
program _ = do
  xs <- fieldInputs @n Public "x"
  fieldOutput "out" $ product $ map var_ xs

altSolve :: ArithCircuit BN128 -> IntMap BN128 -> IntMap BN128
altSolve p inputs =
  evalArithCircuit
    (\w m -> IntMap.lookup (wireName w) m)
    (\w m -> IntMap.insert (wireName w) m)
    p
    inputs
