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
    Ground (..),
    type NBits,
  )
where

import Circuit.Arithmetic
import Data.Field.Galois (GaloisField, PrimeField (fromP))
import Data.Map qualified as Map
import Data.Semiring (Ring (..), Semiring (..))
import Data.Vector.Sized qualified as SV
import Protolude hiding (Semiring)
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)

data Val f ty where
  ValField :: f -> Val f f
  ValBool :: f -> Val f Bool

deriving instance (Show f) => Show (Val f ty)

instance (Pretty f) => Pretty (Val f ty) where
  pretty (ValField f) = pretty f
  pretty (ValBool b) = pretty b

data Var i f ty where
  VarField :: i -> Var i f f
  VarBool :: i -> Var i f Bool

deriving instance (Show i, Show f) => Show (Var i f ty)

instance (Pretty i) => Pretty (Var i f ty) where
  pretty (VarField f) = pretty f
  pretty (VarBool b) = pretty b

rawWire :: Var i f ty -> i
rawWire (VarField i) = i
rawWire (VarBool i) = i

data UnOp f a where
  UNeg :: UnOp f f
  UNot :: UnOp f Bool

deriving instance (Show f) => Show (UnOp f a)

instance Pretty (UnOp f a) where
  pretty op = case op of
    UNeg -> text "neg"
    UNot -> text "!"

data BinOp f a where
  BAdd :: BinOp f f
  BSub :: BinOp f f
  BMul :: BinOp f f
  BDiv :: BinOp f f
  BAnd :: BinOp f Bool
  BOr :: BinOp f Bool
  BXor :: BinOp f Bool

deriving instance (Show f) => Show (BinOp f a)

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
  EVal :: Val f ty -> Expr i f ty
  EVar :: Var i f ty -> Expr i f ty
  EUnOp :: UnOp f ty -> Expr i f ty -> Expr i f ty
  EBinOp :: BinOp f ty -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EIf :: Expr i f Bool -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EEq :: Expr i f f -> Expr i f f -> Expr i f Bool
  ESplit :: (KnownNat (NBits f)) => Expr i f f -> Expr i f (SV.Vector (NBits f) Bool)
  EJoin :: (KnownNat n) => Expr i f (SV.Vector n Bool) -> Expr i f f
  EBundle :: SV.Vector n (Expr i f ty) -> Expr i f (SV.Vector n ty)

instance (Pretty f, Pretty i) => Pretty (Expr i f ty) where
  pretty = prettyPrec 0
    where
      prettyPrec :: Int -> Expr i f ty -> Doc
      prettyPrec p e =
        case e of
          EVal v ->
            pretty v
          EVar v ->
            pretty v
          -- TODO correct precedence
          EUnOp op e1 -> parens (pretty op <+> pretty e1)
          EBinOp op e1 e2 ->
            parensPrec (opPrecedence op) p $
              prettyPrec (opPrecedence op) e1
                <+> pretty op
                <+> prettyPrec (opPrecedence op) e2
          EIf b true false ->
            parensPrec 4 p (text "if" <+> pretty b <+> text "then" <+> pretty true <+> text "else" <+> pretty false)
          -- TODO correct precedence
          EEq l r ->
            parensPrec 1 p (pretty l) <+> text "=" <+> parensPrec 1 p (pretty r)
          ESplit i -> text "split" <+> parens (pretty i)
          EBundle b -> text "bundle" <+> parens (pretty (SV.toList b))
          EJoin i -> text "join" <+> parens (pretty i)

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
  EVal v -> pure $ case v of
    ValBool b -> b == 1
    ValField f -> f
  EVar var -> do
    m <- get
    pure $ case var of
      VarField i -> do
        case Map.lookup i m of
          Just v -> v
          Nothing -> panic $ "TODO: incorrect var lookup: " <> Protolude.show i
      VarBool i ->
        case Map.lookup i m of
          Just v -> v == 1
          Nothing -> panic $ "TODO: incorrect var lookup: " <> Protolude.show i
  EUnOp UNeg e1 ->
    Protolude.negate <$> evalExpr' e1
  EUnOp UNot e1 ->
    not <$> evalExpr' e1
  EBinOp op e1 e2 -> do
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
  EIf b true false -> do
    cond <- evalExpr' b
    if cond
      then evalExpr' true
      else evalExpr' false
  EEq lhs rhs -> do
    lhs' <- evalExpr' lhs
    rhs' <- evalExpr' rhs
    pure $ lhs' == rhs'
  ESplit i -> do
    x <- evalExpr' i
    pure $ SV.generate $ \_ix -> testBit (fromP x) (fromIntegral _ix)
  EBundle as -> traverse evalExpr' as
  EJoin i -> do
    bits <- evalExpr' i
    pure $
      SV.ifoldl (\acc _ix b -> acc + if b then fromInteger (2 ^ fromIntegral @_ @Integer _ix) else 0) 0 bits

instance (GaloisField f) => Semiring (Expr Wire f f) where
  plus = EBinOp BAdd
  zero = EVal $ ValField 0
  times = EBinOp BMul
  one = EVal $ ValField 1

instance (GaloisField f) => Ring (Expr Wire f f) where
  negate = EUnOp UNeg

instance (GaloisField f) => Num (Expr Wire f f) where
  (+) = plus
  (*) = times
  (-) = EBinOp BSub
  negate = EUnOp UNeg
  abs = identity
  signum = const 1
  fromInteger = EVal . ValField . fromInteger
