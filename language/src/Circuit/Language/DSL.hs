{-# LANGUAGE TypeFamilies #-}

-- | Surface language
module Circuit.Language.DSL
  ( Signal,
    cField,
    cBool,
    add_,
    adds_,
    sub_,
    subs_,
    mul_,
    muls_,
    div_,
    divs_,
    and_,
    ands_,
    or_,
    ors_,
    xor_,
    xors_,
    neg_,
    negs_,
    not_,
    nots_,
    eq_,
    neq_,
    fieldInput,
    fieldInputs,
    boolInput,
    boolInputs,
    fieldOutput,
    boolOutput,
    fieldOutputs,
    boolOutputs,
    compileWithWire,
    split_,
    join_,
    truncate_,
    rotate_,
    shift_,
    unbundle_,

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

import Circuit.Arithmetic (Gate (Boolean), InputType (Private, Public), Wire (..))
import Circuit.Language.Compile
import Circuit.Language.Expr
import Data.Field.Galois (GaloisField)
import Data.Maybe (fromJust)
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as SV
import GHC.TypeNats (type (+))
import Protolude

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
add_, sub_, mul_, div_ :: (Hashable f) => Signal f 'TField -> Signal f 'TField -> Signal f 'TField
add_ = binOp_ BAdd
sub_ = binOp_ BSub
mul_ = binOp_ BMul
div_ = binOp_ BDiv

adds_,
  subs_,
  muls_,
  divs_ ::
    (Hashable f) =>
    Signal f ('TVec n 'TField) ->
    Signal f ('TVec n 'TField) ->
    Signal f ('TVec n 'TField)
adds_ = binOp_ BAdds
subs_ = binOp_ BSubs
muls_ = binOp_ BMuls
divs_ = binOp_ BDivs

-- | Binary logic operations on expressions
-- Have to use underscore or similar to avoid shadowing @and@ and @or@
-- from Prelude/Protolude.
and_, or_, xor_ :: (Hashable f) => Signal f 'TBool -> Signal f 'TBool -> Signal f 'TBool
and_ = binOp_ BAnd
or_ = binOp_ BOr
xor_ = binOp_ BXor

ands_,
  ors_,
  xors_ ::
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

neq_ :: (Hashable f) => Signal f 'TField -> Signal f 'TField -> Signal f 'TBool
neq_ a b = not_ (eq_ a b)

nots_ :: (Hashable f) => Signal f ('TVec n 'TBool) -> Signal f ('TVec n 'TBool)
nots_ = unOp_ UNots

neg_ :: (Hashable f) => Signal f 'TField -> Signal f 'TField
neg_ = unOp_ UNeg

negs_ :: (Hashable f) => Signal f ('TVec n 'TField) -> Signal f ('TVec n 'TField)
negs_ = unOp_ UNegs

fieldInput :: InputType -> Text -> ExprM f (Var Wire f 'TField)
fieldInput it label = do
  reserveBinding label
  case it of
    Public -> VarField <$> freshPublicInput label Nothing
    Private -> VarField <$> freshPrivateInput label Nothing
{-# INLINE fieldInput #-}

fieldInputs :: (KnownNat n) => InputType -> Text -> ExprM f (Vector n (Var Wire f 'TField))
fieldInputs it label = do
  reserveBinding label
  case it of
    Public ->
      SV.generateM
        ( \fin ->
            let i = Just $ fromIntegral fin
             in VarField <$> freshPublicInput label i
        )
    Private ->
      SV.generateM
        ( \fin ->
            let i = Just $ fromIntegral fin
             in VarField <$> freshPrivateInput label i
        )
{-# INLINE fieldInputs #-}

boolInput :: InputType -> Text -> ExprM f (Var Wire f 'TBool)
boolInput it label = do
  reserveBinding label
  case it of
    Public -> VarBool <$> freshPublicInput label Nothing
    Private -> VarBool <$> freshPrivateInput label Nothing
{-# INLINE boolInput #-}

boolInputs :: (KnownNat n) => InputType -> Text -> ExprM f (Vector n (Var Wire f 'TBool))
boolInputs it label = do
  reserveBinding label
  let f fin =
        let i = Just $ fromIntegral fin
         in case it of
              Public -> freshPublicInput label i
              Private -> freshPrivateInput label i
   in SV.generateM $ \fin -> do
        w <- f fin
        emit $ Boolean w
        pure $ VarBool w
{-# INLINE boolInputs #-}

fieldOutput :: (Hashable f, GaloisField f) => Text -> Signal f 'TField -> ExprM f (Var Wire f 'TField)
fieldOutput label s = do
  reserveBinding label
  out <- VarField <$> freshOutput label Nothing
  compileWithWire out s
{-# INLINE fieldOutput #-}

fieldOutputs ::
  forall n f.
  (KnownNat n, Hashable f, GaloisField f) =>
  Text ->
  Signal f ('TVec n 'TField) ->
  ExprM f (Vector n (Var Wire f 'TField))
fieldOutputs label s = do
  reserveBinding label
  vs <- SV.generateM @n $ \fin ->
    let i = Just $ fromIntegral fin
     in VarField <$> freshOutput label i
  fromJust . SV.toSized <$> compileWithWires (SV.fromSized vs) s

boolOutput :: forall f. (Hashable f, GaloisField f) => Text -> Signal f 'TBool -> ExprM f (Var Wire f 'TBool)
boolOutput label s = do
  reserveBinding label
  out <- VarBool <$> freshOutput label Nothing
  res <- compileWithWire (boolToField @(Var Wire f 'TBool) out) (boolToField s)
  pure $ coerceVar res
{-# INLINE boolOutput #-}

boolOutputs ::
  forall n f.
  (KnownNat n, Hashable f, GaloisField f) =>
  Text ->
  Signal f ('TVec n 'TBool) ->
  ExprM f (Vector n (Var Wire f 'TBool))
boolOutputs label s = do
  reserveBinding label
  vs <- SV.generateM @n $ \fin ->
    let i = Just $ fromIntegral fin
     in VarBool <$> freshOutput label i
  out <-
    fromJust . SV.toSized @n
      <$> compileWithWires (SV.fromSized $ map (boolToField @(Var Wire f 'TBool)) vs) s
  pure $ map coerceVar out

truncate_ ::
  forall f ty n m.
  (KnownNat m) =>
  (KnownNat (m + n)) =>
  (Hashable f) =>
  Signal f ('TVec (m + n) ty) ->
  Signal f ('TVec m ty)
truncate_ v = do
  bundle_ $ SV.take @m $ unbundle_ v

coerceVar :: Var i f 'TField -> Var i f 'TBool
coerceVar (VarField f) = VarBool f

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
  Add_ a <> Add_ b = Add_ $ add_ a b

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

unbundle_ ::
  forall n f ty.
  (KnownNat n) =>
  (Hashable f) =>
  Expr Wire f (TVec n ty) ->
  SV.Vector n (Expr Wire f ty)
unbundle_ b = SV.generate $ atIndex_ b
