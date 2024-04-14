module Circuit.Solver (solve) where

import Circuit.Affine
import Circuit.Arithmetic
import Data.Field.Galois (PrimeField (fromP), pow)
import Data.Map qualified as Map
import Data.Propagator
import Data.Propagator.Cell (unify)
import Data.Propagator.Num
import Data.Set qualified as Set
import Protolude

--------------------------------------------------------------------------------

newtype SolverEnv s f = SolverEnv
  { vars :: Map Int (Cell s f)
  }

affineCircuitToCell ::
  (PropagatedNum f, Fractional f, Eq f) =>
  SolverEnv s f ->
  AffineCircuit f Wire ->
  ST s (Cell s f)
affineCircuitToCell env (Add a b) = do
  a' <- affineCircuitToCell env a
  b' <- affineCircuitToCell env b
  c <- cell
  cplus a' b' c
  pure c
affineCircuitToCell env (ScalarMul c a) = do
  a' <- affineCircuitToCell env a
  c' <- known c
  p <- cell
  ctimesFractional c' a' p
  pure p
affineCircuitToCell _ (ConstGate c) = known c
affineCircuitToCell env (Var i) =
  pure $ assertLookupCell env (wireName i)
affineCircuitToCell _ Nil = cell

gateToPropagator ::
  (PropagatedNum f, PrimeField f) =>
  SolverEnv s f ->
  Gate f Wire ->
  ST s ()
gateToPropagator env (Mul a b o) = do
  aCell <- affineCircuitToCell env a
  bCell <- affineCircuitToCell env b
  let oCell = assertLookupCell env (wireName o)
  ctimesFractional aCell bCell oCell
gateToPropagator env (Equal i m o) = do
  let iCell = assertLookupCell env (wireName i)
      mCell = assertLookupCell env (wireName m)
      oCell = assertLookupCell env (wireName o)
  watch iCell $ \val -> do
    write oCell $ if val == 0 then 0 else 1
    write mCell $ if val == 0 then 0 else recip val
gateToPropagator env (Split i outs) = do
  let os = zip outs [0 ..]
      iCell = assertLookupCell env (wireName i)
  -- If we know i, we can update the outputs. The reverse is only possible if
  -- if this is a complete binary decomposition (we don't assume so)
  for_ os $ \(o, idx) -> do
    let oCell = assertLookupCell env (wireName o)
    watch iCell $ \val ->
      write oCell $ bool2val $ testBit (fromP val) idx
  -- if we know any of the outputs, we can update a summand of i
  let f acc (o, idx) = do
        let oCell = assertLookupCell env (wireName o)
        summand <- do
          summand <- cell
          coeff <- known (2 `pow` idx)
          ctimesFractional oCell coeff summand
          pure summand
        acc' <- cell
        cplus acc summand acc'
        pure acc'
  seed <- known 0
  s <- foldM f seed os
  unify s iCell
  where
    bool2val True = 1
    bool2val False = 0

solve ::
  forall k.
  (PrimeField k) =>
  (PropagatedNum k) =>
  Map Int k ->
  ArithCircuit k ->
  Map Int k
solve initialAssignments (ArithCircuit gates) = runST $ do
  let wireNames = foldMap (foldMap $ Set.singleton . wireName) gates
  env <- SolverEnv <$> foldlM (\m i -> Map.insert i <$> cell <*> pure m) mempty wireNames
  for_ gates $ gateToPropagator env
  for_ (Map.toList initialAssignments) $ \(v, a) -> do
    -- its possible that the input variables aren't even used in the circuit,
    -- in which case we'd get Nothing
    case Map.lookup v (vars env) of
      Nothing -> pure ()
      Just vCell -> write vCell a
  bindings <-
    foldlM
      ( \m v -> do
          ma <- content $ assertLookupCell env v
          pure $ maybe m (\a -> Map.insert v a m) ma
      )
      mempty
      wireNames
  pure $ bindings `Map.union` initialAssignments

assertLookupCell :: SolverEnv s f -> Int -> Cell s f
assertLookupCell env i = do
  case Map.lookup i (vars env) of
    Nothing -> panic $ "Wire not found: " <> show i
    Just c -> c
