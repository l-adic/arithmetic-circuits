-- | Definition of arithmetic circuits: one with a single
-- multiplication gate with affine inputs and another variant with an
-- arbitrary number of such gates.
module Circuit.Arithmetic
  ( Gate (..),
    outputWires,
    ArithCircuit (..),
    validArithCircuit,
    Wire (..),
    InputType (..),
    wireName,
    evalGate,
    evalArithCircuit,
    unsplit,
    CircuitVars (..),
    relabel,
    collectCircuitVars,
    assignInputs,
    lookupVar,
    booleanWires,
    nGates,
    InputBindings (..),
    insertInputBinding,
    Reindexable (..),
    restrictVars,
  )
where

import Circuit.Affine
  ( AffineCircuit (..),
    evalAffineCircuit,
  )
import Data.Aeson (FromJSON, ToJSON)
import Data.Binary (Binary)
import Data.Field.Galois (PrimeField, fromP)
import Data.IntMap qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Protolude
import Text.PrettyPrint.Leijen.Text as PP
  ( Pretty (..),
    hsep,
    list,
    parens,
    text,
    vcat,
    (<+>),
  )

data InputType = Public | Private deriving (Show, Eq, Ord, Generic, NFData)

instance FromJSON InputType

instance ToJSON InputType

instance Binary InputType

-- | Wires are can be labeled in the ways given in this data type
data Wire
  = InputWire Text InputType Int
  | IntermediateWire Int
  | OutputWire Int
  deriving (Show, Eq, Ord, Generic, NFData)

instance FromJSON Wire

instance ToJSON Wire

instance Hashable Wire where
  hashWithSalt s w = s `hashWithSalt` (0 :: Int) `hashWithSalt` (wireName w)

instance Binary Wire

instance Pretty Wire where
  pretty (InputWire label t v) =
    let a = case t of
          Public -> "pub"
          Private -> "priv"
        suffix = if Text.null label then "" else "_" <> label
     in text (a <> "_input_") <> pretty v <> pretty suffix
  pretty (IntermediateWire v) = text "imm_" <> pretty v
  pretty (OutputWire v) = text "output_" <> pretty v

wireName :: Wire -> Int
wireName (InputWire _ _ v) = v
wireName (IntermediateWire v) = v
wireName (OutputWire v) = v
{-# INLINE wireName #-}

-- | An arithmetic circuit with a single multiplication gate.
data Gate f i
  = Mul
      { mulLeft :: AffineCircuit f i,
        mulRight :: AffineCircuit f i,
        mulOutput :: i
      }
  | Equal
      { eqInput :: i,
        eqMagic :: i,
        eqOutput :: i
      }
  | Split
      { splitInput :: i,
        splitOutputs :: [i]
      }
  | Boolean i
  deriving (Show, Eq, Ord, Generic, NFData, FromJSON, ToJSON)

deriving instance Functor (Gate f)

deriving instance Foldable (Gate f)

deriving instance Traversable (Gate f)

instance (Binary i, Binary f) => Binary (Gate f i)

instance Bifunctor Gate where
  bimap f g = \case
    Mul l r o -> Mul (bimap f g l) (bimap f g r) (g o)
    Equal i m o -> Equal (g i) (g m) (g o)
    Split i os -> Split (g i) (map g os)
    Boolean o -> Boolean (g o)

-- | List output wires of a gate
outputWires :: Gate f i -> [i]
outputWires = \case
  Mul _ _ out -> [out]
  Equal _ _ out -> [out]
  Split _ outs -> outs
  Boolean _ -> []

instance (Pretty i, Pretty f) => Pretty (Gate f i) where
  pretty (Mul l r o) =
    hsep
      [ pretty o,
        text ":=",
        parens (pretty l),
        text "*",
        parens (pretty r)
      ]
  pretty (Equal i _ o) =
    hsep
      [ pretty o,
        text ":=",
        pretty i,
        text "== 0 ? 0 : 1"
      ]
  pretty (Split inp outputs) =
    hsep
      [ PP.list (map pretty outputs),
        text ":=",
        text "split",
        pretty inp
      ]
  pretty (Boolean o) = pretty o <> text ":= bool"

{-# SCC evalGate #-}

-- | Evaluate a single gate
evalGate ::
  (PrimeField f, Show i) =>
  -- | lookup a value at a wire
  (i -> vars -> Maybe f) ->
  -- | update a value at a wire
  (i -> f -> vars -> vars) ->
  -- | context before evaluation
  vars ->
  -- | gate
  Gate f i ->
  -- | context after evaluation
  vars
evalGate _lookupVar _updateVar vars gate =
  case gate of
    Mul l r outputWire ->
      let lval = evalAffineCircuit _lookupVar vars l
          rval = evalAffineCircuit _lookupVar vars r
          res = lval * rval
       in _updateVar outputWire res vars
    Equal i m outputWire ->
      case _lookupVar i vars of
        Nothing ->
          panic "evalGate: the impossible happened"
        Just inp ->
          let res = if inp == 0 then 0 else 1
              mid = if inp == 0 then 0 else recip inp
           in _updateVar outputWire res $
                _updateVar m mid vars
    Split i os ->
      case _lookupVar i vars of
        Nothing ->
          panic "evalGate: the impossible happened"
        Just inp ->
          let bool2val True = 1
              bool2val False = 0
              setWire (ix, oldEnv) currentOut =
                ( ix + 1,
                  _updateVar currentOut (bool2val $ testBit (fromP inp) ix) oldEnv
                )
           in snd . foldl setWire (0, vars) $ os
    Boolean i ->
      case _lookupVar i vars of
        Nothing ->
          panic "evalGate: the impossible happened"
        Just inp ->
          if not (inp == 0 || inp == 1)
            then panic $ "evalGate: boolean input is not 0 or 1: " <> show inp
            else vars

-- | A circuit is a list of multiplication gates along with their
-- output wire labels (which can be intermediate or actual outputs).
newtype ArithCircuit f = ArithCircuit [Gate f Wire]
  deriving (Eq, Show, Generic)
  deriving (NFData) via ([Gate f Wire])

instance (FromJSON f) => FromJSON (ArithCircuit f)

instance (ToJSON f) => ToJSON (ArithCircuit f)

instance (Binary f) => Binary (ArithCircuit f)

instance Functor ArithCircuit where
  fmap f (ArithCircuit gates) = ArithCircuit $ map (first f) gates

instance (Pretty f) => Pretty (ArithCircuit f) where
  pretty (ArithCircuit gs) = vcat . map pretty $ gs

-- | Check whether an arithmetic circuit does not refer to
-- intermediate wires before they are defined and whether output wires
-- are not used as input wires.
validArithCircuit ::
  ArithCircuit f -> Bool
validArithCircuit (ArithCircuit gates) =
  noRefsToUndefinedWires
  where
    noRefsToUndefinedWires =
      fst $
        foldl
          ( \(res, definedWires) gate ->
              ( res
                  && all isNotInput (outputWires gate)
                  && all (validWire definedWires) (fetchVarsGate gate),
                outputWires gate ++ definedWires
              )
          )
          (True, [])
          gates
    isNotInput InputWire {} = False
    isNotInput (OutputWire _) = True
    isNotInput (IntermediateWire _) = True
    validWire _ InputWire {} = True
    validWire _ (OutputWire _) = False
    validWire definedWires i@(IntermediateWire _) = i `elem` definedWires
    fetchVarsGate (Mul l r _) = toList l <> toList r
    fetchVarsGate (Equal i _ _) = [i] -- we can ignore the magic
    -- variable "m", as it is filled
    -- in when evaluating the circuit
    fetchVarsGate (Split i _) = [i]
    fetchVarsGate (Boolean i) = [i]

{-# SCC evalArithCircuit #-}

-- | Evaluate an arithmetic circuit on a given environment containing
-- the inputs. Outputs the entire environment (outputs, intermediate
-- values and inputs).
evalArithCircuit ::
  forall f vars.
  (PrimeField f) =>
  -- | lookup a value at a wire
  (Wire -> vars -> Maybe f) ->
  -- | update a value at a wire
  (Wire -> f -> vars -> vars) ->
  -- | circuit to evaluate
  ArithCircuit f ->
  -- | input variables
  vars ->
  -- | input and output variables
  vars
evalArithCircuit _lookupVar _updateVar (ArithCircuit gates) vars =
  foldl' (evalGate _lookupVar _updateVar) vars gates

-- | Turn a binary expansion back into a single value.
unsplit ::
  (Num f) =>
  -- | (binary) wires containing a binary expansion,
  -- small-endian
  [Wire] ->
  AffineCircuit f Wire
unsplit = snd . foldl (\(ix, rest) wire -> (ix + (1 :: Integer), Add rest (ScalarMul (2 ^ ix) (Var wire)))) (0, ConstGate 0)

data CircuitVars label = CircuitVars
  { cvVars :: IntSet,
    cvPrivateInputs :: IntSet,
    cvPublicInputs :: IntSet,
    cvOutputs :: IntSet,
    cvInputsLabels :: InputBindings label
  }
  deriving (Show, Generic, NFData)

instance (Binary label) => Binary (CircuitVars label)

instance (Pretty label) => Pretty (CircuitVars label) where
  pretty CircuitVars {cvVars, cvPrivateInputs, cvPublicInputs, cvOutputs, cvInputsLabels} =
    vcat
      [ text "vars:" <+> pretty (IntSet.toList cvVars),
        text "private inputs:" <+> pretty (IntSet.toList cvPrivateInputs),
        text "public inputs:" <+> pretty (IntSet.toList cvPublicInputs),
        text "outputs:" <+> pretty (IntSet.toList cvOutputs),
        text "input labels:" <+> pretty cvInputsLabels
      ]

instance (Ord label) => Semigroup (CircuitVars label) where
  a <> b =
    CircuitVars
      { cvVars = cvVars a <> cvVars b,
        cvPrivateInputs = cvPrivateInputs a <> cvPrivateInputs b,
        cvPublicInputs = cvPublicInputs a <> cvPublicInputs b,
        cvOutputs = cvOutputs a <> cvOutputs b,
        cvInputsLabels = cvInputsLabels a <> cvInputsLabels b
      }

instance (Ord label) => Monoid (CircuitVars label) where
  mempty =
    CircuitVars
      { cvVars = mempty,
        cvPrivateInputs = mempty,
        cvPublicInputs = mempty,
        cvOutputs = mempty,
        cvInputsLabels = mempty
      }

instance Reindexable (CircuitVars label) where
  reindex f CircuitVars {..} =
    CircuitVars
      { cvVars = IntSet.map g cvVars,
        cvPrivateInputs = IntSet.map g cvPrivateInputs,
        cvPublicInputs = IntSet.map g cvPublicInputs,
        cvOutputs = IntSet.map g cvOutputs,
        cvInputsLabels = reindex f cvInputsLabels
      }
    where
      g i = fromMaybe i $ IntMap.lookup i f

relabel :: (Ord l2) => (l1 -> l2) -> CircuitVars l1 -> CircuitVars l2
relabel f (CircuitVars vars priv pub outs labels) =
  CircuitVars
    { cvVars = vars,
      cvPrivateInputs = priv,
      cvPublicInputs = pub,
      cvOutputs = outs,
      cvInputsLabels = mapLabels f labels
    }

collectCircuitVars :: ArithCircuit f -> CircuitVars Text
collectCircuitVars (ArithCircuit gates) =
  let f (pubInputs, privInputs, intermediates, outputs, labels) w = case w of
        InputWire label it i -> case it of
          Public -> (IntSet.insert i pubInputs, privInputs, intermediates, outputs, (label, i) : labels)
          Private -> (pubInputs, IntSet.insert i privInputs, intermediates, outputs, labels)
        IntermediateWire i -> (pubInputs, privInputs, IntSet.insert i intermediates, outputs, labels)
        OutputWire i -> (pubInputs, privInputs, intermediates, IntSet.insert i outputs, labels)
      (pubis, prvis, imms, os, ls) = foldMap (foldl f mempty) gates
   in CircuitVars
        { cvVars = IntSet.unions [pubis, prvis, imms, os],
          cvPrivateInputs = prvis,
          cvPublicInputs = pubis,
          cvOutputs = os,
          cvInputsLabels = inputBindingsFromList ls
        }

restrictVars :: CircuitVars label -> IntSet -> CircuitVars label
restrictVars CircuitVars {..} vars =
  CircuitVars
    { cvVars = IntSet.intersection cvVars vars,
      cvPrivateInputs = IntSet.intersection cvPrivateInputs vars,
      cvPublicInputs = IntSet.intersection cvPublicInputs vars,
      cvOutputs = IntSet.intersection cvOutputs vars,
      cvInputsLabels = restrictInputBindings vars cvInputsLabels
    }

assignInputs :: (Ord label) => CircuitVars label -> Map label f -> IntMap f
assignInputs CircuitVars {..} inputs =
  IntMap.mapMaybe (\label -> Map.lookup label inputs) (varToLabel cvInputsLabels)

lookupVar :: (Ord label) => CircuitVars label -> label -> IntMap f -> Maybe f
lookupVar vs label sol = do
  let labelBindings = labelToVar $ cvInputsLabels vs
  var <- Map.lookup label labelBindings
  IntMap.lookup var sol

booleanWires :: ArithCircuit f -> Set Wire
booleanWires (ArithCircuit gates) = foldMap f gates
  where
    f (Boolean i) = Set.singleton i
    f _ = mempty

nGates :: ArithCircuit f -> Int
nGates (ArithCircuit gates) = length gates

--------------------------------------------------------------------------------
data InputBindings label = InputBindings
  { labelToVar :: Map label Int,
    varToLabel :: IntMap label
  }
  deriving (Show, Generic, NFData)

instance (Binary label) => Binary (InputBindings label)

mapLabels :: (Ord l2) => (l1 -> l2) -> InputBindings l1 -> InputBindings l2
mapLabels f InputBindings {labelToVar, varToLabel} =
  InputBindings
    { labelToVar = Map.mapKeys f labelToVar,
      varToLabel = fmap f varToLabel
    }

instance Reindexable (InputBindings label) where
  reindex f InputBindings {..} =
    InputBindings
      { labelToVar = Map.mapMaybe (flip IntMap.lookup f) labelToVar,
        varToLabel = IntMap.compose varToLabel (reverseMap f)
      }
    where
      reverseMap :: IntMap Int -> IntMap Int
      reverseMap = IntMap.foldlWithKey' (\acc k v -> IntMap.insert v k acc) mempty

instance (Ord label) => Semigroup (InputBindings label) where
  a <> b =
    InputBindings
      { labelToVar = labelToVar a <> labelToVar b,
        varToLabel = varToLabel a <> varToLabel b
      }

instance (Ord label) => Monoid (InputBindings label) where
  mempty =
    InputBindings
      { labelToVar = mempty,
        varToLabel = mempty
      }

instance (Pretty label) => Pretty (InputBindings label) where
  pretty InputBindings {labelToVar} =
    pretty $ Map.toList labelToVar

insertInputBinding :: (Ord label) => label -> Int -> InputBindings label -> InputBindings label
insertInputBinding label var InputBindings {..} =
  InputBindings
    { labelToVar = Map.insert label var labelToVar,
      varToLabel = IntMap.insert var label varToLabel
    }

inputBindingsFromList :: (Ord label) => [(label, Int)] -> InputBindings label
inputBindingsFromList = foldl' (flip $ uncurry insertInputBinding) mempty

restrictInputBindings :: IntSet -> InputBindings label -> InputBindings label
restrictInputBindings s InputBindings {..} =
  InputBindings
    { labelToVar = Map.filter (\a -> a `IntSet.member` s) labelToVar,
      varToLabel = IntMap.restrictKeys varToLabel s
    }

--------------------------------------------------------------------------------

class Reindexable a where
  reindex :: IntMap Int -> a -> a

instance Reindexable Wire where
  reindex f = \case
    InputWire l t i -> InputWire l t (g i)
    IntermediateWire i -> IntermediateWire (g i)
    OutputWire i -> OutputWire (g i)
    where
      g i = fromMaybe i $ IntMap.lookup i f

instance Reindexable (AffineCircuit f Wire) where
  reindex f (Add l r) = Add (reindex f l) (reindex f r)
  reindex f (Var i) = Var $ reindex f i
  reindex _ a = a

instance Reindexable (Gate f Wire) where
  reindex f (Mul l r o) = Mul (reindex f l) (reindex f r) (reindex f o)
  reindex f (Equal i m o) = Equal (reindex f i) (reindex f m) (reindex f o)
  reindex f (Split i os) = Split (reindex f i) (reindex f <$> os)
  reindex f (Boolean i) = Boolean (reindex f i)

instance Reindexable (ArithCircuit f) where
  reindex f (ArithCircuit gs) = ArithCircuit (reindex f <$> gs)
