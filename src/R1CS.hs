module R1CS
  ( LinearPoly (..),
    R1C (..),
    R1CS (..),
    Witness (..),
    Inputs (..),
    toR1CS,
    oneVar,
    validateWitness,
    isValidWitness,
    calculateWitness,
  )
where

import Circuit (AffineCircuit (..), ArithCircuit (..), CircuitVars (..), Gate (..), Wire (..), solve, unsplit, wireName)
import Data.Aeson (FromJSON, ToJSON)
import Data.Field.Galois (PrimeField)
import Data.Map qualified as Map
import Data.Propagator (PropagatedNum)
import Data.Set qualified as Set
import Protolude
import Text.PrettyPrint.Leijen.Text (Pretty (..), parens, vsep, (<+>))

-- linear polynomials. By convention, the variable '0' is always substituted with the value '1'.
newtype LinearPoly f = LinearPoly (Map Int f) deriving (Eq, Show, Generic)

instance (ToJSON f) => ToJSON (LinearPoly f)

instance (FromJSON f) => FromJSON (LinearPoly f)

deriving instance Functor LinearPoly

oneVar :: Int
oneVar = 0

instance (Pretty f, Eq f, Num f) => Pretty (LinearPoly f) where
  pretty (LinearPoly m) =
    let summands =
          map mkCoeffPair $
            filter (\(_, coeff) -> coeff /= 0) $
              Map.toList m
     in case summands of
          [] -> "0"
          [x] -> x
          x : xs -> foldl (\acc a -> acc <+> "+" <+> a) x xs
    where
      mkVar var
        | var == oneVar = "1"
        | otherwise = pretty $ "x_" <> pretty var
      mkCoeffPair (var, coeff)
        | var == oneVar && coeff == 1 = "1"
        | coeff == 1 = mkVar var
        | var == oneVar = pretty coeff
        | otherwise = pretty coeff <+> "*" <+> "x_" <> pretty var

-- constant polynomial equal 'c'
constant :: f -> LinearPoly f
constant = LinearPoly . Map.singleton oneVar

-- | The polynomial equal variable 'x'
monomial :: (f, Int) -> LinearPoly f
monomial (coeff, var) = LinearPoly $ Map.singleton var coeff

instance (Num f) => Semigroup (LinearPoly f) where
  LinearPoly l <> LinearPoly r = LinearPoly $ Map.unionWith (+) l r

instance (Num f) => Monoid (LinearPoly f) where
  mempty = LinearPoly mempty

substitute :: (Num f) => LinearPoly f -> Map Int f -> f
substitute (LinearPoly m) vals =
  let f acc var coeff = acc + coeff * Map.findWithDefault 0 var vals
   in Map.foldlWithKey f 0 m

mkLinearPoly :: (Num f) => AffineCircuit f Wire -> LinearPoly f
mkLinearPoly = \case
  Add l r -> mkLinearPoly l <> mkLinearPoly r
  ScalarMul c a -> (c *) <$> mkLinearPoly a
  ConstGate c -> constant c
  Var i -> monomial (1, wireName i)
  Nil -> panic "Nil AffineCircuit does not have an arithmetic representation"

newtype R1C f = R1C (LinearPoly f, LinearPoly f, LinearPoly f) deriving (Eq, Show, Generic)

instance (ToJSON f) => ToJSON (R1C f)

instance (FromJSON f) => FromJSON (R1C f)

instance (Eq f, Num f, Pretty f) => Pretty (R1C f) where
  pretty (R1C (aV, bV, cV)) =
    parens (pretty aV) <+> "*" <+> parens (pretty bV) <+> "==" <+> pretty cV

mkR1C :: (Num f) => Gate f Wire -> R1C f
mkR1C = \case
  Mul l r o -> R1C (mkLinearPoly l, mkLinearPoly r, monomial (1, wireName o))
  Equal i m o -> R1C (monomial (1, wireName i), monomial (1, wireName m), monomial (1, wireName o))
  Split i outs -> R1C (constant 1, mkLinearPoly $ unsplit outs, monomial (1, wireName i))

data R1CS f = R1CS
  { r1csConstraints :: [R1C f],
    r1csNumVars :: Int,
    r1csNumPublicInputs :: Int,
    r1csNumPrivateInputs :: Int,
    r1csNumOutputs :: Int
  }
  deriving (Show)

instance (Eq f, Num f, Pretty f) => Pretty (R1CS f) where
  pretty (R1CS {r1csConstraints}) = vsep (pretty <$> r1csConstraints)

newtype Inputs f = Inputs (Map Int f)
  deriving (Eq, Show, Generic)

instance (ToJSON f) => ToJSON (Inputs f)

instance (FromJSON f) => FromJSON (Inputs f)

instance (Pretty f) => Pretty (Inputs f) where
  pretty (Inputs m) = vsep $ map mkPair $ Map.toList m
    where
      mkPair (var, val) = pretty var <+> ":=" <+> pretty val

newtype Witness f = Witness (Map Int f) deriving (Eq, Show, Generic)

instance (ToJSON f) => ToJSON (Witness f)

instance (FromJSON f) => FromJSON (Witness f)

instance (Pretty f) => Pretty (Witness f) where
  pretty (Witness m) = vsep $ map mkPair $ Map.toList m
    where
      mkPair (var, val) = pretty var <+> ":=" <+> pretty val

validateWitness :: (Eq f, Num f) => Witness f -> R1CS f -> Either (R1C f) ()
validateWitness (Witness w) (R1CS {r1csConstraints}) =
  let f r1c = unless (satisfiesR1C r1c) (Left r1c)
   in traverse_ f r1csConstraints
  where
    w' = Map.insert oneVar 1 w
    satisfiesR1C (R1C (a, b, c)) = substitute a w' * substitute b w' == substitute c w'

isValidWitness :: (Eq f, Num f) => Witness f -> R1CS f -> Bool
isValidWitness w r1cs = isRight $ validateWitness w r1cs

toR1CS :: (Num f) => CircuitVars l -> ArithCircuit f -> R1CS f
toR1CS CircuitVars {..} (ArithCircuit gates) =
  R1CS
    { r1csConstraints = mkR1C <$> gates,
      r1csNumVars = Set.size $ Set.insert oneVar cvVars,
      r1csNumPublicInputs = Set.size cvPublicInputs,
      r1csNumPrivateInputs = Set.size cvPrivateInputs,
      r1csNumOutputs = Set.size cvOutputs
    }

calculateWitness ::
  forall f l.
  (PrimeField f) =>
  (PropagatedNum f) =>
  CircuitVars l ->
  ArithCircuit f ->
  Inputs f ->
  (R1CS f, Witness f)
calculateWitness vars circuit (Inputs m) =
  let r1cs = toR1CS vars circuit
      w = solve vars circuit (Map.insert oneVar 1 m)
   in (r1cs, Witness w)
