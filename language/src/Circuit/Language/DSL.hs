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
    boolsInput,
    fieldsInput,
    retBools,
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
and_, or_, xor_ :: (Eq f, Num f) => Signal f Bool -> Signal f Bool -> Signal f Bool
and_ a b = case (a,b) of 
  (EVal (ValBool 0), _) -> cBool False
  (_, EVal (ValBool 0)) -> cBool False
  (EVal (ValBool 1), EVal (ValBool 1)) -> cBool True
  _ -> EBinOp BAnd a b

or_ a b = case (a,b) of 
  (EVal (ValBool 1), _) -> cBool True
  (_, EVal (ValBool 1)) -> cBool True
  (EVal (ValBool 0), EVal (ValBool 0)) -> cBool False
  _ -> EBinOp BOr a b


xor_ a b = case (a,b) of 
  (EVal (ValBool 0), x) -> x
  (x, EVal (ValBool 0)) -> x
  (EVal (ValBool _a), EVal (ValBool _b)) -> 
    if _a == 1 
      then cBool $ _b /= 1
      else cBool (_b == 1)
  _ -> EBinOp BXor a b

-- | Negate expression
not_ :: Num f => Signal f Bool -> Signal f Bool
not_ a = case a of
  EVal (ValBool b) -> EVal $ ValBool $ 1 - b
  _ -> EUnOp UNot a

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

boolsInput :: (KnownNat n) => InputType -> Text -> ExprM f (Vector n (Var Wire f Bool))
boolsInput it label = SV.generateM $ \i -> boolInput it $ label <> show (fromIntegral @_ @Int i)

fieldsInput :: (KnownNat n) => InputType -> Text -> ExprM f (Vector n (Var Wire f f))
fieldsInput it label = SV.generateM $ \i -> fieldInput it $ label <> show (fromIntegral @_ @Int i)

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

retBools :: forall n f. 
  (KnownNat n, GaloisField f, Hashable f) => 
  Text -> 
  Signal f (Vector n Bool) -> 
  ExprM f (Vector n (Var Wire f Bool))
retBools label sig = fromJust . SV.toSized . unsafeCoerce <$> do
  compileWithWires (SV.fromSized <$> fieldsInput @n Public label) sig

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

instance (Eq f, Num f) => Semigroup (Any_ f) where
  Any_ a <> Any_ b = Any_ $ or_ a b

instance (Eq f, Num f) => Monoid (Any_ f) where
  mempty = Any_ $ cBool False

newtype Add_ f = Add_ {unAdd_ :: Signal f f}

instance (GaloisField f) => Semigroup (Add_ f) where
  Add_ a <> Add_ b = Add_ $ add a b

instance (GaloisField f) => Monoid (Add_ f) where
  mempty = Add_ $ cField 0

newtype XOr_ f = XOr_ {unXOr_ :: Signal f Bool}

instance (Eq f, Num f) => Semigroup (XOr_ f) where
  XOr_ a <> XOr_ b = XOr_ $ xor_ a b

instance (Eq f, Num f) => Monoid (XOr_ f) where
  mempty = XOr_ $ cBool False

--------------------------------------------------------------------------------

elem_ ::
  (Eq f, Num f, Foldable t) =>
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
  (Eq f, Num f, Foldable t) =>
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
