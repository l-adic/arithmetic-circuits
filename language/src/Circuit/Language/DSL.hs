{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Surface language
module Circuit.Language.DSL
  ( Signal,
    Bundled (..),
    type Unbundled,
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
    truncate_,
    rotateRight,
    rotateLeft,

    -- * Monoids
    Any_ (..),
    And_ (..),
    Add_ (..),
    XOr_ (..),
    elem_,
    any_,
    all_,
  )
where

import Circuit.Arithmetic (InputType (Private, Public), Wire (..))
import Circuit.Language.Compile
import Circuit.Language.TExpr
import Data.Field.Galois (GaloisField, Prime, PrimeField)
import Data.Finite (Finite)
import Data.Maybe (fromJust)
import Data.Vector.Sized (Vector, ix)
import Data.Vector.Sized qualified as SV
import GHC.TypeNats (type (+))
import Lens.Micro ((.~), (^.))
import Protolude
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
type Signal f = Expr Wire f

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
  Signal f (Vector (NBits f) Bool)
splitBits = ESplit

joinBits :: (KnownNat n) => Signal f (Vector n Bool) -> Signal f f
joinBits = EJoin

deref :: Var Wire f ty -> Signal f ty
deref = EVar

retBool :: (GaloisField f, Hashable f) => Text -> Signal f Bool -> ExprM f (Var Wire f Bool)
retBool label sig = compileWithWire (boolInput Public label) sig

retField :: (PrimeField f, Hashable f) => Text -> Signal f f -> ExprM f (Var Wire f f)
retField label sig = compileWithWire (fieldInput Public label) sig

atIndex ::
  (Bundled f (Vector n ty)) =>
  Finite n ->
  Signal f (Vector n ty) ->
  ExprM f (Signal f ty)
atIndex i b = do
  bs <- unbundle b
  return $ bs ^. ix i

updateIndex_ ::
  (Bundled f (Vector n ty)) =>
  Finite n ->
  Signal f ty ->
  Signal f (Vector n ty) ->
  ExprM f (Signal f (Vector n ty))
updateIndex_ p s v = do
  bs <- unbundle v
  let bs' = bs & ix p .~ s
  return $ bundle bs'

truncate_ ::
  forall f ty n m.
  (Bundled f (Vector (m + n) ty)) =>
  (Bundled f (Vector m ty)) =>
  (KnownNat m) =>
  Signal f (Vector (m + n) ty) ->
  ExprM f (Signal f (Vector m ty))
truncate_ v = do
  as <- unbundle v
  let bs = SV.take as
  return $ bundle bs

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

newtype Add_ f = Add_ {unAdd_ :: Signal f f}

instance (GaloisField f) => Semigroup (Add_ f) where
  Add_ a <> Add_ b = Add_ $ add a b

instance (GaloisField f) => Monoid (Add_ f) where
  mempty = Add_ $ cField 0

newtype XOr_ f = XOr_ {unXOr_ :: Signal f Bool}

instance Semigroup (XOr_ f) where
  XOr_ a <> XOr_ b = XOr_ $ xor_ a b

instance (Num f) => Monoid (XOr_ f) where
  mempty = XOr_ $ cBool False

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

--------------------------------------------------------------------------------

type family Unbundled f a = res | res -> a where
  Unbundled f (Vector n ty) = Vector n (Signal f ty)

class Bundled f a where
  bundle :: Unbundled f a -> Signal f a
  unbundle :: Signal f a -> ExprM f (Unbundled f a)

instance (KnownNat p, KnownNat n) => Bundled (Prime p) (Vector n (Prime p)) where
  bundle = EBundle
  unbundle = _unBundle

instance (Hashable f, GaloisField f, KnownNat n) => Bundled f (Vector n Bool) where
  bundle = EBundle
  unbundle = fmap unsafeCoerce . _unBundle

--------------------------------------------------------------------------------

rotateRight ::
  forall n d a.
  (KnownNat d) =>
  (KnownNat n) =>
  Vector n a ->
  Finite d ->
  Vector n a
rotateRight xs d =
  fromJust $ SV.fromList $ rotateList (fromIntegral d) $ SV.toList xs

rotateLeft ::
  forall n d a.
  (KnownNat d) =>
  (KnownNat n) =>
  Vector n a ->
  Finite d ->
  Vector n a
rotateLeft xs d = 
  fromJust $ SV.fromList $ rotateList (negate $ fromIntegral d) $ SV.toList xs

rotateList :: Int -> [a] -> [a]
rotateList steps x = 
  let n = length x
  in take n $ drop (steps `mod` n) $ cycle x