{-# LANGUAGE TypeFamilies #-}

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
    updateIndex_,
    bundle,
    unBundle,
    boolToField,

    -- * Monoids
    Any_ (..),
    And_ (..),
    elem_,
    any_,
    all_,
  )
where

import Circuit.Arithmetic (InputType (Private, Public), Wire (..))
import Circuit.Expr
import Data.Field.Galois (GaloisField)
import Data.Finite (Finite)
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as V
import Protolude
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
type Signal f a = Expr Wire f a

type Bundle f n a = Expr Wire f (Vector n a)

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
  (KnownNat (NBits f)) =>
  Signal f f ->
  Bundle f (NBits f) Bool
splitBits = ESplit

joinBits :: (KnownNat n) => Bundle f n Bool -> Signal f f
joinBits = EJoin

deref :: Var Wire f ty -> Signal f ty
deref = EVar

retBool :: (Num f) => Text -> Signal f Bool -> ExprM f Wire
retBool label sig = compileWithWire (boolInput Public label) sig

retField :: (Num f) => Text -> Signal f f -> ExprM f Wire
retField label sig = compileWithWire (fieldInput Public label) sig

atIndex :: (KnownNat n, Ground f ty) => Bundle f n ty -> Finite n -> Signal f ty
atIndex = EAtIndex

updateIndex_ :: (KnownNat n, Ground f ty) => Finite n -> Signal f ty -> Bundle f n ty -> Bundle f n ty
updateIndex_ p = EUpdateIndex p

bundle :: (Ground f ty) => Vector n (Signal f ty) -> Bundle f n ty
bundle = EBundle

unBundle :: (KnownNat n, Ground f ty) => Bundle f n ty -> Vector n (Signal f ty)
unBundle b = V.generate $ atIndex b

boolToField :: Signal f Bool -> Signal f f
boolToField = unsafeCoerce

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
