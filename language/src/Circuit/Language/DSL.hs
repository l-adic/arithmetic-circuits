{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Surface language
module Circuit.Language.DSL
  ( Signal,
    Bundle (..),
    cField,
    cBool,
    add,
    sub,
    mul,
    and_,
    ands_,
    or_,
    ors_,
    xor_,
    xors_,
    not_,
    nots_,
    eq_,
    fieldInput,
    boolInput,
    fieldOutput,
    boolOutput,
    fieldsOutput,
    boolsOutput,
    compileWithWire,
    split_,
    join_,
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
import Circuit.Language.Expr
import Data.Field.Galois (GaloisField)
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
cField :: (Hashable f) => f -> Signal f 'TField
cField = val_ . ValField
{-# INLINE cField #-}

cBool :: (Hashable f, Num f) => Bool -> Signal f 'TBool
cBool b = val_ . ValBool $ if b then 1 else 0
{-# INLINE cBool #-}

-- | Binary arithmetic operations on expressions
add, sub, mul :: (Hashable f, Num f) => Signal f 'TField -> Signal f 'TField -> Signal f 'TField
add = (+)
sub = (-)
mul = (*)

-- | Binary logic operations on expressions
-- Have to use underscore or similar to avoid shadowing @and@ and @or@
-- from Prelude/Protolude.
and_, or_, xor_ :: (Hashable f) => Signal f 'TBool -> Signal f 'TBool -> Signal f 'TBool
and_ = binOp_ BAnd
or_ = binOp_ BOr
xor_ = binOp_ BXor

ands_, ors_, xors_ ::
  (Hashable f) =>
  Signal f ('TVec n 'TBool) ->
  Signal f ('TVec n 'TBool) ->
  Signal f ('TVec n 'TBool)
ands_ = binOp_ BAnds
ors_ = binOp_ BOrs
xors_ = binOp_ BXors

-- | Negate expression
not_ :: (Hashable f) => Signal f 'TBool -> Signal f 'TBool
not_ = unOp_ UNot

nots_ :: (Hashable f) => Signal f ('TVec n 'TBool) -> Signal f ('TVec n 'TBool)
nots_ = unOp_ UNots

fieldInput :: InputType -> Text -> ExprM f (Var Wire f 'TField)
fieldInput it label =
  case it of
    Public -> VarField <$> freshPublicInput label
    Private -> VarField <$> freshPrivateInput label
{-# INLINE fieldInput #-}

boolInput :: InputType -> Text -> ExprM f (Var Wire f 'TBool)
boolInput it label = case it of
  Public -> VarBool <$> freshPublicInput label
  Private -> VarBool <$> freshPrivateInput label
{-# INLINE boolInput #-}

fieldOutput :: (Hashable f, GaloisField f) => Text -> Signal f 'TField -> ExprM f (Var Wire f 'TField)
fieldOutput label s = do
  out <- VarField <$> freshOutput label
  compileWithWire out s
{-# INLINE fieldOutput #-}

fieldsOutput :: (KnownNat n, Hashable f, GaloisField f) => Vector n (Var Wire f 'TField) -> Signal f ('TVec n 'TField) -> ExprM f (Vector n (Var Wire f 'TField))
fieldsOutput vs s = fromJust . SV.toSized <$> compileWithWires (SV.fromSized vs) s

boolOutput :: forall f. (Hashable f, GaloisField f) => Text -> Signal f 'TBool -> ExprM f (Var Wire f 'TBool)
boolOutput label s = do
  out <- VarBool <$> freshOutput label
  unsafeCoerce <$> compileWithWire (boolToField @(Var Wire f 'TBool) out) (boolToField s)
{-# INLINE boolOutput #-}

boolsOutput :: (KnownNat n, Hashable f, GaloisField f) => Vector n (Var Wire f 'TBool) -> Signal f ('TVec n 'TBool) -> ExprM f (Vector n (Var Wire f 'TBool))
boolsOutput vs s = unsafeCoerce <$> fieldsOutput (boolToField <$> vs) (boolToField s)

atIndex ::
  (Bundle f ('TVec n ty)) =>
  (Unbundled f (TVec n ty) ~ Vector n (Signal f ty)) =>
  Finite n ->
  Signal f ('TVec n ty) ->
  ExprM f (Signal f ty)
atIndex i b = do
  bs <- unbundle b
  return $ bs ^. ix i

updateIndex_ ::
  (Bundle f ('TVec n ty)) =>
  (Unbundled f (TVec n ty) ~ Vector n (Signal f ty)) =>
  Finite n ->
  Signal f ty ->
  Signal f ('TVec n ty) ->
  ExprM f (Signal f ('TVec n ty))
updateIndex_ p s v = do
  bs <- unbundle v
  let bs' = bs & ix p .~ s
  return $ bundle bs'

truncate_ ::
  forall f ty n m.
  (Bundle f ('TVec (m + n) ty)) =>
  (Bundle f ('TVec m ty)) =>
  (Unbundled f (TVec (m + n) ty) ~ Vector (m + n) (Signal f ty)) =>
  (Unbundled f (TVec m ty) ~ Vector m (Signal f ty)) =>
  (KnownNat m) =>
  Signal f ('TVec (m + n) ty) ->
  ExprM f (Signal f ('TVec m ty))
truncate_ v = do
  as <- unbundle v
  let bs = SV.take @m as
  return $ bundle bs

--------------------------------------------------------------------------------

newtype And_ f = And_ {unAnd_ :: Signal f 'TBool}

instance (Hashable f) => Semigroup (And_ f) where
  And_ a <> And_ b = And_ $ binOp_ BAnd a b

instance (Num f, Hashable f) => Monoid (And_ f) where
  mempty = And_ $ cBool True

newtype Any_ f = Any_ {unAny_ :: Signal f 'TBool}

instance (Num f, Hashable f) => Semigroup (Any_ f) where
  Any_ a <> Any_ b = Any_ $ or_ a b

instance (Eq f, Num f, Hashable f) => Monoid (Any_ f) where
  mempty = Any_ $ cBool False

newtype Add_ f = Add_ {unAdd_ :: Signal f 'TField}

instance (Hashable f, Num f) => Semigroup (Add_ f) where
  Add_ a <> Add_ b = Add_ $ add a b

instance (Hashable f, Num f) => Monoid (Add_ f) where
  mempty = Add_ $ cField 0

newtype XOr_ f = XOr_ {unXOr_ :: Signal f 'TBool}

instance (Hashable f, Num f) => Semigroup (XOr_ f) where
  XOr_ a <> XOr_ b = XOr_ $ xor_ a b

instance (Eq f, Num f, Hashable f) => Monoid (XOr_ f) where
  mempty = XOr_ $ cBool False

--------------------------------------------------------------------------------

elem_ ::
  (Num f, Foldable t, Hashable f) =>
  Signal f 'TField ->
  t (Signal f 'TField) ->
  Signal f 'TBool
elem_ a as =
  let f b = eq_ a b
   in any_ f as

all_ ::
  (Num f, Foldable t, Hashable f) =>
  (a -> Signal f 'TBool) ->
  t a ->
  Signal f 'TBool
all_ f = unAnd_ . foldMap (And_ . f)

any_ ::
  (Num f, Foldable t, Hashable f) =>
  (a -> Signal f 'TBool) ->
  t a ->
  Signal f 'TBool
any_ f = unAny_ . foldMap (Any_ . f)

--------------------------------------------------------------------------------

class Bundle f a where
  type Unbundled f a = r | r -> a
  bundle :: Unbundled f a -> Signal f a
  unbundle :: Signal f a -> ExprM f (Unbundled f a)

instance (Hashable f, GaloisField f, KnownNat n) => Bundle f ('TVec n 'TField) where
  type Unbundled f ('TVec n 'TField) = Vector n (Signal f 'TField)
  bundle = bundle_
  unbundle = _unBundle

instance (Hashable f, GaloisField f, KnownNat n) => Bundle f ('TVec n 'TBool) where
  type Unbundled f ('TVec n 'TBool) = Vector n (Signal f 'TBool)
  bundle = bundle_
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
