-- | Surface language
module Circuit.Lang
  ( cField,
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
    ret,
    -- fieldVar,
    -- boolVar,
    fieldInput,
    boolInput,
    cond,
    compileWithWire,
    withBits,
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
import Data.Type.Nat qualified as Nat
import Data.Vec.Lazy (Vec)
import Protolude

-- | Convert constant to expression
cField :: f -> Expr Wire f f
cField = EVal . ValField

cBool :: (Num f) => Bool -> Expr Wire f Bool
cBool b = EVal . ValBool $ if b then 1 else 0

-- | Binary arithmetic operations on expressions
add, sub, mul :: Expr Wire f f -> Expr Wire f f -> Expr Wire f f
add = EBinOp BAdd
sub = EBinOp BSub
mul = EBinOp BMul

-- | Binary logic operations on expressions
-- Have to use underscore or similar to avoid shadowing @and@ and @or@
-- from Prelude/Protolude.
and_, or_, xor_ :: Expr Wire f Bool -> Expr Wire f Bool -> Expr Wire f Bool
and_ = EBinOp BAnd
or_ = EBinOp BOr
xor_ = EBinOp BXor

-- | Negate expression
not_ :: Expr Wire f Bool -> Expr Wire f Bool
not_ = EUnOp UNot

-- | Compare two expressions
eq :: Expr Wire f f -> Expr Wire f f -> Expr Wire f Bool
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
cond :: Expr Wire f Bool -> Expr Wire f ty -> Expr Wire f ty -> Expr Wire f ty
cond = EIf

withBits ::
  (Nat.SNatI (NBits f)) =>
  Expr Wire f f ->
  (Vec (NBits f) (Expr Wire f Bool) -> Expr Wire f ty) ->
  Expr Wire f ty
withBits = ESplit

deref :: Var Wire f ty -> Expr Wire f ty
deref = EVar

compileWithWire :: (Num f) => ExprM f (Var Wire f ty) -> Expr Wire f ty -> ExprM f Wire
compileWithWire freshWire expr = do
  compileOut <- compile expr
  case compileOut of
    Left wire -> do
      wire' <- rawWire <$> freshWire
      emit $ Mul (ConstGate 1) (Var wire') wire
      pure wire
    Right circ -> do
      wire <- rawWire <$> freshWire
      emit $ Mul (ConstGate 1) circ wire
      pure wire

ret :: (Num f) => Text -> Expr Wire f Bool -> ExprM f Wire
ret label = compileWithWire (boolInput Public label)

--------------------------------------------------------------------------------

newtype And_ f = And_ {unAnd_ :: Expr Wire f Bool}

instance Semigroup (And_ f) where
  And_ a <> And_ b = And_ $ EBinOp BAnd a b

instance (Num f) => Monoid (And_ f) where
  mempty = And_ $ cBool True

newtype Any_ f = Any_ {unAny_ :: Expr Wire f Bool}

instance Semigroup (Any_ f) where
  Any_ a <> Any_ b = Any_ $ or_ a b

instance (Num f) => Monoid (Any_ f) where
  mempty = Any_ $ cBool False

--------------------------------------------------------------------------------

elem_ ::
  (Num f, Foldable t) =>
  Expr Wire f f ->
  t (Expr Wire f f) ->
  Expr Wire f Bool
elem_ a as =
  let f b = eq a b
   in any_ f as

all_ ::
  (Num f, Foldable t) =>
  (a -> Expr Wire f Bool) ->
  t a ->
  Expr Wire f Bool
all_ f = unAnd_ . foldMap (And_ . f)

any_ ::
  (Num f, Foldable t) =>
  (a -> Expr Wire f Bool) ->
  t a ->
  Expr Wire f Bool
any_ f = unAny_ . foldMap (Any_ . f)
