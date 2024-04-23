-- | Surface language
module Circuit.Lang
  ( Signal,
    Bundle,
    cField,
    cBool,
    add,
    sub,
    mul,
    and_,
    or_,
    xor_,
    not_,
    eq,
    deref,
    retBool,
    retField,
    fieldInput,
    boolInput,
    cond,
    compileWithWire,
    splitBits,
    joinBits,
    atIndex,
    Any_ (..),
    And_ (..),
    elem_,
    any_,
    all_,
  )
where

import Circuit.Affine (AffineCircuit (..))
import Circuit.Arithmetic (Gate (..), InputType (Private, Public), Wire (..))
import Circuit.Expr
import Data.Field.Galois (GaloisField)
import Data.Fin (Fin)
import Data.Type.Nat qualified as Nat
import Data.Vec.Lazy (Vec)
import Protolude

--------------------------------------------------------------------------------

type Signal f a = Expr Wire f Identity a

type Bundle f n a = Expr Wire f (Vec n) a

-- | Convert constant to expression
cField :: f -> Signal f f
cField = EVal . ValField

cBool :: (Num f) => Bool -> Signal f Bool
cBool b = EVal . ValBool $ if b then 1 else 0

-- | Binary arithmetic operations on expressions
add, sub, mul :: (GaloisField f) => Signal f f -> Signal f f -> Signal f f
add = (+)
sub = (-)
mul = (*)

-- | Binary logic operations on expressions
-- Have to use underscore or similar to avoid shadowing @and@ and @or@
-- from Prelude/Protolude.
and_, or_, xor_ :: Signal f Bool -> Signal f Bool -> Signal f Bool
and_ = EBinOp BAnd
or_ = EBinOp BOr
xor_ = EBinOp BXor

-- | Negate expression
not_ :: Signal f Bool -> Signal f Bool
not_ = EUnOp UNot

-- | Compare two expressions
eq :: Signal f f -> Signal f f -> Signal f Bool
eq = EEq

fieldInput :: InputType -> Text -> ExprM f (Var Wire f f)
fieldInput it label = case it of
  Public -> VarField <$> freshPublicInput label
  Private -> VarField <$> freshPrivateInput label

boolInput :: InputType -> Text -> ExprM f (Var Wire f Bool)
boolInput it label = case it of
  Public -> VarBool <$> freshPublicInput label
  Private -> VarBool <$> freshPrivateInput label

-- | Conditional statement on expressions
cond :: Signal f Bool -> Signal f ty -> Signal f ty -> Signal f ty
cond = EIf

splitBits ::
  (Nat.SNatI (NBits f)) =>
  Signal f f ->
  Bundle f (NBits f) Bool
splitBits = ESplit

joinBits :: (Num f, Nat.SNatI n) => Bundle f n Bool -> Signal f f
joinBits = EJoin

deref :: Var Wire f ty -> Signal f ty
deref = EVar

compileWithWire :: (Num f) => ExprM f (Var Wire f ty) -> Signal f ty -> ExprM f Wire
compileWithWire freshWire expr = do
  compileOut <- runIdentity <$> compile expr
  case compileOut of
    Left wire -> do
      wire' <- rawWire <$> freshWire
      emit $ Mul (ConstGate 1) (Var wire') wire
      pure wire
    Right circ -> do
      wire <- rawWire <$> freshWire
      emit $ Mul (ConstGate 1) circ wire
      pure wire

retBool :: (Num f) => Text -> Signal f Bool -> ExprM f Wire
retBool label = compileWithWire (boolInput Public label)

retField :: (Num f) => Text -> Signal f f -> ExprM f Wire
retField label = compileWithWire (fieldInput Public label)

atIndex :: (Nat.SNatI n) => Bundle f n ty -> Fin n -> Signal f ty
atIndex = EAtIndex

--------------------------------------------------------------------------------

newtype And_ f = And_ {unAnd_ :: Signal f Bool}

instance Semigroup (And_ f) where
  And_ a <> And_ b = And_ $ EBinOp BAnd a b

instance (Num f) => Monoid (And_ f) where
  mempty = And_ $ cBool True

newtype Any_ f = Any_ {unAny_ :: Signal f Bool}

instance Semigroup (Any_ f) where
  Any_ a <> Any_ b = Any_ $ or_ a b

instance (Num f) => Monoid (Any_ f) where
  mempty = Any_ $ cBool False

--------------------------------------------------------------------------------

elem_ ::
  (Num f, Foldable t) =>
  Signal f f ->
  t (Signal f f) ->
  Signal f Bool
elem_ a as =
  let f b = eq a b
   in any_ f as

all_ ::
  (Num f, Foldable t) =>
  (a -> Signal f Bool) ->
  t a ->
  Signal f Bool
all_ f = unAnd_ . foldMap (And_ . f)

any_ ::
  (Num f, Foldable t) =>
  (a -> Signal f Bool) ->
  t a ->
  Signal f Bool
any_ f = unAny_ . foldMap (Any_ . f)
