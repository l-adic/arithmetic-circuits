-- | Definition of arithmetic circuits that only contain addition,
-- scalar multiplications and constant gates, along with its direct
-- evaluation and translation into affine maps.
module Circuit.Affine
  ( AffineCircuit (..),
    evalAffineCircuit,
    affineCircuitToAffineMap,
    evalAffineMap,
    dotProduct,
  )
where

import           Data.Aeson                   (FromJSON, ToJSON)
import qualified Data.Map                     as Map
import           Protolude
import           Text.PrettyPrint.Leijen.Text (Doc, Pretty(..), parens, text,
                                               (<+>))

-- | Arithmetic circuits without multiplication, i.e. circuits
-- describe affine transformations.
data AffineCircuit f i
  = Add (AffineCircuit f i) (AffineCircuit f i)
  | ScalarMul f (AffineCircuit f i)
  | ConstGate f
  | Var i
  deriving (Read, Eq, Ord, Show, Generic, NFData)

instance (FromJSON i, FromJSON f) => FromJSON (AffineCircuit f i)
instance (ToJSON i, ToJSON f) => ToJSON (AffineCircuit f i)

deriving instance Functor (AffineCircuit f)
deriving instance Foldable (AffineCircuit f)
deriving instance Traversable (AffineCircuit f)

instance Bifunctor AffineCircuit where
  bimap f g = \case
    Add l r -> Add (bimap f g l) (bimap f g r)
    ScalarMul s x -> ScalarMul (f s) (bimap f g x)
    ConstGate c -> ConstGate (f c)
    Var i -> Var (g i)

instance (Pretty i, Show f) => Pretty (AffineCircuit f i) where
  pretty = prettyPrec 0
    where
      prettyPrec :: Int -> AffineCircuit f i -> Doc
      prettyPrec p e =
        case e of
          Var v ->
            pretty v
          ConstGate f ->
            text $ show f
          ScalarMul f e1 ->
            text (show f) <+> text "*" <+> parensPrec 7 p (prettyPrec p e1)
          Add e1 e2 ->
            parensPrec 6 p $
              prettyPrec 6 e1
                <+> text "+"
                <+> prettyPrec 6 e2

parensPrec :: Int -> Int -> Doc -> Doc
parensPrec opPrec p = if p > opPrec then parens else identity

-- | Evaluate the arithmetic circuit without mul-gates on the given
-- input. Variable map is assumed to have all the variables referred
-- to in the circuit. Failed lookups are currently treated as 0.
evalAffineCircuit ::
  Num f =>
  -- | lookup function for variable mapping
  (i -> vars -> Maybe f) ->
  -- | variables
  vars ->
  -- | circuit to evaluate
  AffineCircuit f i ->
  f
evalAffineCircuit lookupVar vars = \case
  ConstGate f -> f
  Var i -> fromMaybe 0 $ lookupVar i vars
  Add l r -> evalAffineCircuit lookupVar vars l + evalAffineCircuit lookupVar vars r
  ScalarMul scalar expr -> evalAffineCircuit lookupVar vars expr * scalar

-- | Convert non-mul circuit to a vector representing the evaluation
-- function. We use a @Map@ to represent the potentially sparse vector.
affineCircuitToAffineMap ::
  (Num f, Ord i) =>
  -- | circuit to translate
  AffineCircuit f i ->
  -- | constant part and non-constant part
  (f, Map i f)
affineCircuitToAffineMap = \case
  Var i -> (0, Map.singleton i 1)
  Add l r -> (constLeft + constRight, Map.unionWith (+) vecLeft vecRight)
    where
      (constLeft, vecLeft) = affineCircuitToAffineMap l
      (constRight, vecRight) = affineCircuitToAffineMap r
  ScalarMul scalar expr -> (scalar * constExpr, fmap (scalar *) vecExpr)
    where
      (constExpr, vecExpr) = affineCircuitToAffineMap expr
  ConstGate f -> (f, Map.empty)

-- | Evaluating the affine map representing the arithmetic circuit
-- without mul-gates against inputs. If the input map does not have a
-- variable that is referred to in the affine map, then it is treated
-- as a 0.
evalAffineMap ::
  (Num f, Ord i) =>
  -- | program split into constant and non-constant part
  (f, Map i f) ->
  -- | input variables
  Map i f ->
  f
evalAffineMap (constPart, linearPart) input =
  constPart + dotProduct linearPart input

dotProduct :: (Num f, Ord i) => Map i f -> Map i f -> f
dotProduct inp comp =
  sum
    . Map.elems
    $ Map.mapWithKey (\ix c -> c * Map.findWithDefault 0 ix inp) comp
