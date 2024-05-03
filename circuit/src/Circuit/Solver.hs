module Circuit.Solver (solve) where

import Circuit.Affine
import Circuit.Arithmetic
import Data.Field.Galois (GaloisField, PrimeField (fromP), pow)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Propagator
import Data.Propagator.Cell (unify)
import Data.Propagator.Num
import Protolude

--------------------------------------------------------------------------------

newtype SolverEnv s f = SolverEnv
  { vars :: IntMap (Cell s f)
  }

{-# SCC affineCircuitToCell #-}
affineCircuitToCell ::
  (GaloisField f) =>
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

{-# SCC gateToPropagator #-}
gateToPropagator ::
  (PrimeField f) =>
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
gateToPropagator _ (Boolean _) = pure ()

{-# SCC solve #-}
solve ::
  forall k l.
  (PrimeField k) =>
  CircuitVars l ->
  ArithCircuit k ->
  IntMap k ->
  IntMap k
solve CircuitVars {cvVars = wireNames} (ArithCircuit gates) initialAssignments = runST $ do
  let wires = IntSet.toList wireNames
  env <- SolverEnv <$> foldlM (\m i -> IntMap.insert i <$> cell <*> pure m) mempty wires
  for_ gates $ gateToPropagator env
  for_ (IntMap.toList initialAssignments) $ \(v, a) -> do
    -- its possible that the input variables aren't even used in the circuit,
    -- in which case we'd get Nothing
    case IntMap.lookup v (vars env) of
      Nothing -> pure ()
      Just vCell -> write vCell a
  bindings <-
    foldlM
      ( \m v -> do
          ma <- content $ assertLookupCell env v
          pure $ maybe m (\a -> IntMap.insert v a m) ma
      )
      mempty
      wires
  pure $ bindings `IntMap.union` initialAssignments

assertLookupCell :: SolverEnv s f -> Int -> Cell s f
assertLookupCell env i = do
  case IntMap.lookup i (vars env) of
    Nothing -> panic $ "Wire not found: " <> show i
    Just c -> c
