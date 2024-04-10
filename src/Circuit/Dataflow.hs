module Circuit.Dataflow
  ( removeUnreachable,
  )
where

import Protolude
import Data.Map qualified as Map
import Data.Set qualified as Set
import Circuit.Arithmetic
  ( ArithCircuit (..),
    Gate (..),
    Wire (..),
    wireName,
  )

newtype GateId = GateId Int
  deriving (Eq, Ord)

newtype Roots a = DEnv {dfRoots :: Set Int}

addRoot :: Int -> State (Roots a) ()
addRoot x = modify (\s -> s {dfRoots = Set.insert x (dfRoots s)})

data Env a = Env
  { gatesMap :: Map GateId (Gate a Wire),
    indexedVars :: Map Int (Set GateId)
  }

-- | Give a unique number (i.e. and index) to each gate
numberGates :: ArithCircuit a -> Map GateId (Gate a Wire)
numberGates (ArithCircuit gates) =
  Map.fromList $ zip (GateId <$> [0 ..]) gates

-- | Creates a mapping from variables to the set of gate IDs in which each variable appears.
indexVars :: Map GateId (Gate a Wire) -> Map Int (Set GateId)
indexVars gateMap = Map.fromListWith (<>) $ do
  (gid, gate) <- Map.toList gateMap
  wire <- toList gate
  pure (wireName wire, Set.singleton gid)

-- | Starting from a list of roots, explore the circuit to find all the gates/wires that are reachable.
-- | Filter the unreachable gates from the circuit.
removeUnreachable ::
  (Ord a) =>
  [Int] ->
  ArithCircuit a ->
  ArithCircuit a
removeUnreachable outVars cs =
  let gatesMap = numberGates cs
      env =
        Env
          { gatesMap,
            indexedVars = indexVars gatesMap
          }
      foundGates =
        flip evalState (DEnv Set.empty) $
          do
            mapM_ addRoot outVars
            -- start searching from the output variables
            exploreVars env outVars
            roots <- gets dfRoots
            pure $ Set.foldl (\acc root -> acc `Set.union` findGates env root) mempty roots
   in ArithCircuit $ Set.toList foundGates
  where
    findGates Env {indexedVars, gatesMap} root =
      Set.fromList $
        let gids = maybe mempty Set.toList $ Map.lookup root indexedVars
         in mapMaybe (`Map.lookup` gatesMap) gids

exploreVars ::
  Env a ->
  [Int] ->
  State (Roots a) ()
exploreVars _ [] = pure ()
exploreVars env@(Env {gatesMap, indexedVars}) (r : rest) =
  case Map.lookup r indexedVars of
    Nothing -> exploreVars env rest
    Just gs -> do
      currentRoots <- gets dfRoots
      let newRoots = Set.toList $ getVars gs Set.\\ currentRoots
      mapM_ addRoot newRoots
      exploreVars env $ newRoots <> rest
  where
    getVars :: Set GateId -> Set Int
    getVars gs = Set.fromList $ do
      gate <- mapMaybe (`Map.lookup` gatesMap) $ Set.toList gs
      wireName <$> toList gate