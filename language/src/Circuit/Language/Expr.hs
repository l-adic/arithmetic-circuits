module Circuit.Language.Expr  
  (  Expr(..),
  UVar(..),
  BinOp(..),
  UnOp(..),
  Hash(..),
  hashCons,
  getAnnotation,
  ) where

import Data.Vector qualified as V
import Protolude hiding (Semiring)

newtype UVar i = UVar i
  deriving (Show, Eq)
  deriving (Hashable) via i

data BinOp = BAdd | BSub | BMul | BDiv | BAnd | BOr | BXor deriving (Show, Eq, Generic)

instance Hashable BinOp

data UnOp = UNeg | UNot deriving (Show, Eq, Generic)

instance Hashable UnOp

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

newtype Hash = Hash Int
  deriving (Show, Eq, Ord)
  deriving (Hashable) via Int

hashCons :: (Hashable i, Hashable f) => Expr () i f -> Expr Hash i f
hashCons = \case
  EVal _ f ->
    let i = Hash $ hash (hash @Text "EVal", f)
     in EVal i f
  EVar _ v ->
    let i = Hash $ hash (hash @Text "EVar", v)
     in EVar i v
  EUnOp _ op e ->
    let e' = hashCons e
        i = Hash $ hash (hash @Text "EUnOp", op, getAnnotation e')
     in EUnOp i op e'
  EBinOp _ op e1 e2 ->
    let e1' = hashCons e1
        e2' = hashCons e2
        i = Hash $ hash (hash @Text "EBinOp", op, getAnnotation e1', getAnnotation e2')
     in EBinOp i op e1' e2'
  EIf _ b t e ->
    let b' = hashCons b
        t' = hashCons t
        e' = hashCons e
        i = Hash $ hash (hash @Text "EIf", getAnnotation b', getAnnotation t', getAnnotation e')
     in EIf i b' t' e'
  EEq _ l r ->
    let l' = hashCons l
        r' = hashCons r
        i = Hash $ hash (hash @Text "EEq", getAnnotation l', getAnnotation r')
     in EEq i l' r'
  ESplit _ n e ->
    let e' = hashCons e
        i = Hash $ hash (hash @Text "ESplit", n, getAnnotation e')
     in ESplit i n e'
  EJoin _ e ->
    let e' = hashCons e
        i = Hash $ hash (hash @Text "EJoin", getAnnotation e')
     in EJoin i e'
  EAtIndex _ v ix ->
    let v' = hashCons v
        i = Hash $ hash (hash @Text "EAtIndex", getAnnotation v', ix)
     in EAtIndex i v' ix
  EUpdateIndex _ p b v ->
    let b' = hashCons b
        v' = hashCons v
        i = Hash $ hash (hash @Text "EUpdateIndex", p, getAnnotation b', getAnnotation v')
     in EUpdateIndex i p b' v'
  EBundle _ b ->
    let b' = V.map hashCons b
        i = Hash $ hash (hash @Text "EBundle", toList $ fmap getAnnotation b')
     in EBundle i b'
