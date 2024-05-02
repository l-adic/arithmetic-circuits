{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Circuit.Language.TExpr
  ( Val (..),
    Var (..),
    UnOp (..),
    BinOp (..),
    Expr (..),
    evalExpr,
    rawWire,
    rawVal,
    Ground (..),
    type NBits,
    getId,
    val,
    var,
    unOp,
    binOp,
    if_,
    eq,
    split,
    join_,
    bundle_,
  )
where

import Data.Field.Galois (PrimeField (fromP))
import Data.Map qualified as Map
import Data.Vector.Sized qualified as SV
import Protolude hiding (Semiring(..))
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)
import Data.Semiring (Semiring(..), Ring(..))

data Val f ty where
  ValField :: f -> Val f f
  ValBool :: f -> Val f Bool

deriving instance (Eq f) => Eq (Val f ty)
deriving instance (Show f) => Show (Val f ty)

instance (Pretty f) => Pretty (Val f ty) where
  pretty (ValField f) = pretty f
  pretty (ValBool b) = pretty b

rawVal :: Val f ty -> f
rawVal (ValField f) = f
rawVal (ValBool f) = f

instance Hashable f => Hashable (Val f ty) where
  hashWithSalt s (ValField f) = s `hashWithSalt ` ("ValField" :: Text) `hashWithSalt` f
  hashWithSalt s (ValBool f) = s `hashWithSalt` ("ValBool" :: Text) `hashWithSalt` f

data Var i f ty where
  VarField :: i -> Var i f f
  VarBool :: i -> Var i f Bool

deriving instance (Eq i) => Eq (Var i f ty)
deriving instance (Show i, Show f) => Show (Var i f ty)

instance (Pretty i) => Pretty (Var i f ty) where
  pretty (VarField f) = pretty f
  pretty (VarBool b) = pretty b

rawWire :: Var i f ty -> i
rawWire (VarField i) = i
rawWire (VarBool i) = i

instance Hashable i => Hashable (Var i f ty) where
  hashWithSalt s (VarField v) = s `hashWithSalt` ("VarField" :: Text) `hashWithSalt` v
  hashWithSalt s (VarBool f) = s `hashWithSalt` ("VarBool" :: Text) `hashWithSalt` f

data UnOp f a where
  UNeg :: UnOp f f
  UNot :: UnOp f Bool

deriving instance (Show f) => Show (UnOp f a)
deriving instance Eq (UnOp f a)

instance Pretty (UnOp f a) where
  pretty op = case op of
    UNeg -> text "neg"
    UNot -> text "!"

instance Hashable (UnOp f a) where
  hashWithSalt s UNeg = s `hashWithSalt` ("UNeg" :: Text)
  hashWithSalt s UNot = s `hashWithSalt` ("UNot" :: Text)

data BinOp f a where
  BAdd :: BinOp f f
  BSub :: BinOp f f
  BMul :: BinOp f f
  BDiv :: BinOp f f
  BAnd :: BinOp f Bool
  BOr :: BinOp f Bool
  BXor :: BinOp f Bool

deriving instance (Show f) => Show (BinOp f a)
deriving instance Eq (BinOp f a)

instance Hashable (BinOp f a) where
  hashWithSalt s BAdd = s `hashWithSalt` ("BAdd" :: Text)
  hashWithSalt s BSub = s `hashWithSalt` ("BSub" :: Text)
  hashWithSalt s BMul = s `hashWithSalt` ("BMul" :: Text)
  hashWithSalt s BDiv = s `hashWithSalt` ("BDiv" :: Text)
  hashWithSalt s BAnd = s `hashWithSalt` ("BAnd" :: Text)
  hashWithSalt s BOr = s `hashWithSalt` ("BOr" :: Text)
  hashWithSalt s BXor = s `hashWithSalt` ("BXor" :: Text)

instance Pretty (BinOp f a) where
  pretty op = case op of
    BAdd -> text "+"
    BSub -> text "-"
    BMul -> text "*"
    BDiv -> text "/"
    BAnd -> text "&&"
    BOr -> text "||"
    BXor -> text "xor"

opPrecedence :: BinOp f a -> Int
opPrecedence BOr = 5
opPrecedence BXor = 5
opPrecedence BAnd = 5
opPrecedence BSub = 6
opPrecedence BAdd = 6
opPrecedence BMul = 7
opPrecedence BDiv = 8

type family NBits a :: Nat

-- | This constring prevents us from building up nested vectors inside the expression type
class Ground (t :: Type -> Type) (ty :: Type) (f :: Type) where
  coerceGroundType :: t ty -> t f
  unsafeCoerceGroundType :: t f -> t ty
  unsafeCoerceGroundType = unsafeCoerce

instance Ground (Expr i f) f f where
  coerceGroundType = identity

instance Ground (Expr i f) Bool f where
  coerceGroundType = unsafeCoerce

instance Ground (Val f) ty f where
  coerceGroundType (ValBool b) = ValField b
  coerceGroundType (ValField f) = ValField f

instance Ground (Var i f) ty f where
  coerceGroundType (VarField i) = VarField i
  coerceGroundType (VarBool i) = VarField i

-- | Expression data type of (arithmetic) expressions over a field @f@
-- with variable names/indices coming from @i@.
data Expr i f ty where
  EVal :: Int -> Val f ty -> Expr i f ty
  EVar :: Int -> Var i f ty -> Expr i f ty
  EUnOp :: Int -> UnOp f ty -> Expr i f ty -> Expr i f ty
  EBinOp :: Int -> BinOp f ty -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EIf :: Int -> Expr i f Bool -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EEq :: Int -> Expr i f f -> Expr i f f -> Expr i f Bool
  ESplit :: (KnownNat (NBits f)) => Int -> Expr i f f -> Expr i f (SV.Vector (NBits f) Bool)
  EJoin :: (KnownNat n) => Int -> Expr i f (SV.Vector n Bool) -> Expr i f f
  EBundle :: Int -> SV.Vector n (Expr i f ty) -> Expr i f (SV.Vector n ty)

deriving instance (Show i, Show f) => Show (Expr i f ty)

getId :: Expr i f ty -> Int
getId (EVal i _) = i
getId (EVar i _) = i
getId (EUnOp i _ _) = i
getId (EBinOp i _ _ _) = i
getId (EIf i _ _ _) = i
getId (EEq i _ _) = i
getId (ESplit i _) = i
getId (EJoin i _) = i
getId (EBundle i _) = i

instance (Pretty f, Pretty i) => Pretty (Expr i f ty) where
  pretty = prettyPrec 0
    where
      prettyPrec :: Int -> Expr i f ty -> Doc
      prettyPrec p e =
        case e of
          EVal _ v ->
            pretty v
          EVar _ v ->
            pretty v
          -- TODO correct precedence
          EUnOp _ op e1 -> parens (pretty op <+> pretty e1)
          EBinOp _ op e1 e2 ->
            parensPrec (opPrecedence op) p $
              prettyPrec (opPrecedence op) e1
                <+> pretty op
                <+> prettyPrec (opPrecedence op) e2
          EIf _ b true false ->
            parensPrec 4 p (text "if" <+> pretty b <+> text "then" <+> pretty true <+> text "else" <+> pretty false)
          -- TODO correct precedence
          EEq _ l r ->
            parensPrec 1 p (pretty l) <+> text "=" <+> parensPrec 1 p (pretty r)
          ESplit _ i -> text "split" <+> parens (pretty i)
          EBundle _ b -> text "bundle" <+> parens (pretty (SV.toList b))
          EJoin _ i -> text "join" <+> parens (pretty i)

parensPrec :: Int -> Int -> Doc -> Doc
parensPrec opPrec p = if p > opPrec then parens else identity

--------------------------------------------------------------------------------

evalExpr :: (PrimeField f, Ord i, Show i) => Map i f -> Expr i f ty -> ty
evalExpr inputs e = evalState (evalExpr' e) inputs

-- | Evaluate arithmetic expressions directly, given an environment
evalExpr' ::
  forall f i ty.
  (PrimeField f, Ord i, Show i) =>
  -- | variable lookup
  -- | expression to evaluate
  Expr i f ty ->
  -- | input values
  -- | resulting value
  State (Map i f) ty
evalExpr' expr = case expr of
  EVal _ v -> pure $ case v of
    ValBool b -> b == 1
    ValField f -> f
  EVar _ _var -> do
    m <- get
    pure $ case _var of
      VarField i -> do
        case Map.lookup i m of
          Just v -> v
          Nothing -> panic $ "TODO: incorrect var lookup: " <> Protolude.show i
      VarBool i ->
        case Map.lookup i m of
          Just v -> v == 1
          Nothing -> panic $ "TODO: incorrect var lookup: " <> Protolude.show i
  EUnOp _ UNeg e1 ->
    Protolude.negate <$> evalExpr' e1
  EUnOp _ UNot e1 ->
    not <$> evalExpr' e1
  EBinOp _ op e1 e2 -> do
    e1' <- evalExpr' e1
    e2' <- evalExpr' e2
    pure $ apply e1' e2'
    where
      apply = case op of
        BAdd -> (+)
        BSub -> (-)
        BMul -> (*)
        BDiv -> (/)
        BAnd -> (&&)
        BOr -> (||)
        BXor -> \x y -> (x || y) && not (x && y)
  EIf _ b true false -> do
    cond <- evalExpr' b
    if cond
      then evalExpr' true
      else evalExpr' false
  EEq _ lhs rhs -> do
    lhs' <- evalExpr' lhs
    rhs' <- evalExpr' rhs
    pure $ lhs' == rhs'
  ESplit _ i -> do
    x <- evalExpr' i
    pure $ SV.generate $ \_ix -> testBit (fromP x) (fromIntegral _ix)
  EBundle _ as -> traverse evalExpr' as
  EJoin _ i -> do
    bits <- evalExpr' i
    pure $
      SV.ifoldl (\acc _ix b -> acc + if b then fromInteger (2 ^ fromIntegral @_ @Integer _ix) else 0) 0 bits

instance (Hashable f, Num f) => Semiring (Expr i f f) where
  plus = binOp BAdd
  zero = val (ValField 0)
  times = binOp BMul
  one = val (ValField 1)

instance (Num f, Hashable f) => Ring (Expr i f f) where
  negate = unOp UNeg

instance (Num f, Hashable f) => Num (Expr i f f) where
  (+) = plus
  (*) = times
  (-) = binOp BSub
  negate = unOp UNeg
  abs = identity
  signum = const 1
  fromInteger = val . ValField . fromInteger


val :: Hashable f => Val f ty -> Expr i f ty
val v = 
  let h = hash v
  in EVal h v

var :: Hashable i => Var i f ty -> Expr i f ty
var v = 
  let h = hash v
  in EVar h v

unOp :: UnOp f a -> Expr i f a -> Expr i f a
unOp op e = 
  let h = hash (op, getId e)
  in EUnOp h op e

binOp :: BinOp f a -> Expr i f a -> Expr i f a -> Expr i f a
binOp op e1 e2 = 
  let h = hash (op, getId e1, getId e2)
  in EBinOp h op e1 e2

if_ :: Expr i f Bool -> Expr i f a -> Expr i f a -> Expr i f a
if_ b t f = 
  let h = hash (getId b, getId t, getId f)
  in EIf h b t f

eq :: Expr i f f -> Expr i f f -> Expr i f Bool
eq l r = 
  let h = hash (getId l, getId r)
  in EEq h l r

split :: KnownNat (NBits f) => Expr i f f -> Expr i f (SV.Vector (NBits f) Bool)
split i = 
  let h = hash (getId i)
  in ESplit h i

join_ :: KnownNat n => Expr i f (SV.Vector n Bool) -> Expr i f f
join_ i = 
  let h = hash (getId i)
  in EJoin h i

bundle_ :: SV.Vector n (Expr i f ty) -> Expr i f (SV.Vector n ty)
bundle_ b = 
  let h = hash (getId <$> b)
  in EBundle h b