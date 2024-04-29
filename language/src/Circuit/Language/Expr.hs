module Circuit.Language.Expr where

import Circuit.Language.TExpr qualified as TExpr
import Data.Vector qualified as V
import Data.Vector.Sized qualified as SV
import Protolude hiding (Semiring)

newtype UVar i = UVar i
  deriving (Show, Eq)
  deriving (Hashable) via i

data BinOp = BAdd | BSub | BMul | BDiv | BAnd | BOr | BXor deriving (Show, Eq, Generic)

instance Hashable BinOp

untypeBinOp :: TExpr.BinOp f a -> BinOp
untypeBinOp = \case
  TExpr.BAdd -> BAdd
  TExpr.BSub -> BSub
  TExpr.BMul -> BMul
  TExpr.BDiv -> BDiv
  TExpr.BAnd -> BAnd
  TExpr.BOr -> BOr
  TExpr.BXor -> BXor

data UnOp = UNeg | UNot deriving (Show, Eq, Generic)

instance Hashable UnOp

untypeUnOp :: TExpr.UnOp f a -> UnOp
untypeUnOp = \case
  TExpr.UNeg -> UNeg
  TExpr.UNot -> UNot

-- a is an annotation
data Expr a i f
  = EVal a f
  | EVar a (UVar i)
  | EUnOp a UnOp (Expr a i f)
  | EBinOp a BinOp (Expr a i f) (Expr a i f)
  | EIf a (Expr a i f) (Expr a i f) (Expr a i f)
  | EEq a (Expr a i f) (Expr a i f)
  | ESplit a Int (Expr a i f)
  | EJoin a (Expr a i f)
  | EAtIndex a (Expr a i f) Int
  | EUpdateIndex a Int (Expr a i f) (Expr a i f)
  | EBundle a (V.Vector (Expr a i f))
  deriving (Eq, Show)

unType :: forall f i ty. TExpr.Expr i f ty -> Expr () i f
unType = \case
  TExpr.EVal v -> case v of
    TExpr.ValBool b -> EVal () b
    TExpr.ValField f -> EVal () f
  TExpr.EVar v -> EVar () (UVar $ TExpr.rawWire v)
  TExpr.EUnOp op e -> EUnOp () (untypeUnOp op) (unType e)
  TExpr.EBinOp op e1 e2 -> EBinOp () (untypeBinOp op) (unType e1) (unType e2)
  TExpr.EIf b t e -> EIf () (unType b) (unType t) (unType e)
  TExpr.EEq l r -> EEq () (unType l) (unType r)
  TExpr.ESplit i -> ESplit () (fromIntegral $ natVal (Proxy @(TExpr.NBits f))) (unType i)
  TExpr.EJoin i -> EJoin () (unType i)
  TExpr.EAtIndex v ix -> EAtIndex () (unType v) (fromIntegral ix)
  TExpr.EUpdateIndex p b v -> EUpdateIndex () (fromIntegral p) (unType b) (unType v)
  TExpr.EBundle b -> EBundle () (unType <$> SV.fromSized b)

getAnnotation :: Expr a i f -> a
getAnnotation = \case
  EVal a _ -> a
  EVar a _ -> a
  EUnOp a _ _ -> a
  EBinOp a _ _ _ -> a
  EIf a _ _ _ -> a
  EEq a _ _ -> a
  ESplit a _ _ -> a
  EJoin a _ -> a
  EAtIndex a _ _ -> a
  EUpdateIndex a _ _ _ -> a
  EBundle a _ -> a

hashCons :: (Hashable i, Hashable f) => Expr () i f -> Expr Int i f
hashCons = \case
  EVal _ f ->
    let i = hash (hash @Text "EVal", f)
     in EVal i f
  EVar _ v ->
    let i = hash (hash @Text "EVar", v)
     in EVar i v
  EUnOp _ op e ->
    let e' = hashCons e
        i = hash (hash @Text "EUnOp", op, getAnnotation e')
     in EUnOp i op e'
  EBinOp _ op e1 e2 ->
    let e1' = hashCons e1
        e2' = hashCons e2
        i = hash (hash @Text "EBinOp", op, getAnnotation e1', getAnnotation e2')
     in EBinOp i op e1' e2'
  EIf _ b t e ->
    let b' = hashCons b
        t' = hashCons t
        e' = hashCons e
        i = hash (hash @Text "EIf", getAnnotation b', getAnnotation t', getAnnotation e')
     in EIf i b' t' e'
  EEq _ l r ->
    let l' = hashCons l
        r' = hashCons r
        i = hash (hash @Text "EEq", getAnnotation l', getAnnotation r')
     in EEq i l' r'
  ESplit _ n e ->
    let e' = hashCons e
        i = hash (hash @Text "ESplit", n, getAnnotation e')
     in ESplit i n e'
  EJoin _ e ->
    let e' = hashCons e
        i = hash (hash @Text "EJoin", getAnnotation e')
     in EJoin i e'
  EAtIndex _ v ix ->
    let v' = hashCons v
        i = hash (hash @Text "AtIndex", getAnnotation v', ix)
     in EAtIndex i v' ix
  EUpdateIndex _ p b v ->
    let b' = hashCons b
        v' = hashCons v
        i = hash (hash @Text "UpdateIndex", p, getAnnotation b', getAnnotation v')
     in EUpdateIndex i p b' v'
  EBundle _ b ->
    let b' = V.map hashCons b
        i = hash (hash @Text "Bundle", toList $ fmap getAnnotation b')
     in EBundle i b'
