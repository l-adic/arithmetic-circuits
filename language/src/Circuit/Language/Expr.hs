{-# LANGUAGE TypeFamilies #-}

module Circuit.Language.Expr
  ( Expr (..),
    UVar (..),
    BinOp (..),
    UnOp (..),
    val,
    var,
    unOp,
    binOp,
    if_,
    eq,
    split,
    join_,
    bundle,
    getId,
    termCache,
  )
where

import Data.Interned
import Data.Vector qualified as V
import Protolude hiding (Semiring)

newtype UVar i = UVar i
  deriving (Show, Eq)

instance (Hashable i) => Hashable (UVar i) where
  hashWithSalt s (UVar i) = s `hashWithSalt` ("UVar" :: Text) `hashWithSalt` i

data BinOp = BAdd | BSub | BMul | BDiv | BAnd | BOr | BXor deriving (Show, Eq, Generic)

instance Hashable BinOp

data UnOp = UNeg | UNot deriving (Show, Eq, Generic)

instance Hashable UnOp

-- a is an annotation
data Expr i f
  = EVal {-# UNPACK #-} !Id !f
  | EVar {-# UNPACK #-} !Id !(UVar i)
  | EUnOp {-# UNPACK #-} !Id !UnOp !(Expr i f)
  | EBinOp {-# UNPACK #-} !Id !BinOp !(Expr i f) !(Expr i f)
  | EIf {-# UNPACK #-} !Id !(Expr i f) !(Expr i f) !(Expr i f)
  | EEq {-# UNPACK #-} !Id !(Expr i f) !(Expr i f)
  | ESplit {-# UNPACK #-} !Id !Int !(Expr i f)
  | EJoin {-# UNPACK #-} !Id !(Expr i f)
  | EBundle {-# UNPACK #-} !Id !(V.Vector (Expr i f))
  deriving (Eq, Show)

getId :: Expr i f -> Id
getId = \case
  EVal a _ -> a
  EVar a _ -> a
  EUnOp a _ _ -> a
  EBinOp a _ _ _ -> a
  EIf a _ _ _ -> a
  EEq a _ _ -> a
  ESplit a _ _ -> a
  EJoin a _ -> a
  EBundle a _ -> a

data CacheExpr i f where
  CEVal :: f -> CacheExpr i f
  CEVar :: UVar i -> CacheExpr i f
  CEUnOp :: UnOp -> Expr i f -> CacheExpr i f
  CEBinOp :: BinOp -> Expr i f -> Expr i f -> CacheExpr i f
  CEIf :: Expr i f -> Expr i f -> Expr i f -> CacheExpr i f
  CEEq :: Expr i f -> Expr i f -> CacheExpr i f
  CESplit :: Int -> Expr i f -> CacheExpr i f
  CEJoin :: Expr i f -> CacheExpr i f
  CEBundle :: V.Vector (Expr i f) -> CacheExpr i f

deriving instance (Show i, Show f) => Show (CacheExpr i f)

termCache :: (Hashable i, Hashable f) => Cache (Expr i f)
termCache = mkCache
{-# NOINLINE termCache #-}

instance (Hashable i, Hashable f) => Interned (Expr i f) where
  type Uninterned (Expr i f) = CacheExpr i f
  data Description (Expr i f)
    = DVal f
    | DVar (UVar i)
    | DUnOp UnOp Id
    | DBinOp BinOp Id Id
    | DIf Id Id Id
    | DEq Id Id
    | DSplit Int Id
    | DJoin Id
    | DBundle Id
    deriving (Show, Eq)
  describe (CEVal v) = DVal v
  describe (CEVar v) = DVar v
  describe (CEUnOp op e) = DUnOp op (getId e)
  describe (CEBinOp op e1 e2) = DBinOp op (getId e1) (getId e2)
  describe (CEIf b t f) = DIf (getId b) (getId t) (getId f)
  describe (CEEq l r) = DEq (getId l) (getId r)
  describe (CESplit n i) = DSplit n (getId i)
  describe (CEJoin i) = DJoin (getId i)
  describe (CEBundle i) = DBundle (hash $ map getId $ toList i)

  identify _id = go
    where
      go (CEVal v) = EVal _id v
      go (CEVar v) = EVar _id v
      go (CEUnOp op e) = EUnOp _id op e
      go (CEBinOp op e1 e2) = EBinOp _id op e1 e2
      go (CEIf b t f) = EIf _id b t f
      go (CEEq l r) = EEq _id l r
      go (CESplit n i) = ESplit _id n i
      go (CEJoin i) = EJoin _id i
      go (CEBundle i) = EBundle _id i

  cache = termCache

instance (Hashable i, Hashable f) => Uninternable (Expr i f) where
  unintern (EVal _ v) = CEVal v
  unintern (EVar _ v) = CEVar v
  unintern (EUnOp _ op e) = CEUnOp op e
  unintern (EBinOp _ op e1 e2) = CEBinOp op e1 e2
  unintern (EIf _ b t f) = CEIf b t f
  unintern (EEq _ l r) = CEEq l r
  unintern (ESplit _ n i) = CESplit n i
  unintern (EJoin _ i) = CEJoin i
  unintern (EBundle _ i) = CEBundle i

instance (Hashable i, Hashable f) => Hashable (Description (Expr i f)) where
  hashWithSalt s (DVal i) = s `hashWithSalt` ("DVal" :: Text) `hashWithSalt` i
  hashWithSalt s (DVar i) = s `hashWithSalt` ("DVar" :: Text) `hashWithSalt` i
  hashWithSalt s (DUnOp i j) = s `hashWithSalt` ("DUnOp" :: Text) `hashWithSalt` i `hashWithSalt` j
  hashWithSalt s (DBinOp i j k) = s `hashWithSalt` ("DBinOp" :: Text) `hashWithSalt` i `hashWithSalt` j `hashWithSalt` k
  hashWithSalt s (DIf i j k) = s `hashWithSalt` ("DIf" :: Text) `hashWithSalt` i `hashWithSalt` j `hashWithSalt` k
  hashWithSalt s (DEq i j) = s `hashWithSalt` ("DEq" :: Text) `hashWithSalt` i `hashWithSalt` j
  hashWithSalt s (DSplit n i) = s `hashWithSalt` ("DSplit" :: Text) `hashWithSalt` n `hashWithSalt` i
  hashWithSalt s (DJoin i) = s `hashWithSalt` ("DJoin" :: Text) `hashWithSalt` i
  hashWithSalt s (DBundle i) = s `hashWithSalt` ("DBundle" :: Text) `hashWithSalt` i

val :: (Hashable i, Hashable f) => f -> Expr i f
val = intern . CEVal
{-# NOINLINE val #-}

var :: (Hashable i, Hashable f) => UVar i -> Expr i f
var = intern . CEVar
{-# NOINLINE var #-}

unOp :: (Hashable i, Hashable f) => UnOp -> Expr i f -> Expr i f
unOp op e = intern $ CEUnOp op e
{-# NOINLINE unOp #-}

binOp :: (Hashable i, Hashable f) => BinOp -> Expr i f -> Expr i f -> Expr i f
binOp op e1 e2 = intern $ CEBinOp op e1 e2
{-# NOINLINE binOp #-}

if_ :: (Hashable i, Hashable f) => Expr i f -> Expr i f -> Expr i f -> Expr i f
if_ b t f = intern $ CEIf b t f
{-# NOINLINE if_ #-}

eq :: (Hashable i, Hashable f) => Expr i f -> Expr i f -> Expr i f
eq l r = intern $ CEEq l r
{-# NOINLINE eq #-}

split :: (Hashable i, Hashable f) => Int -> Expr i f -> Expr i f
split n i = intern $ CESplit n i
{-# NOINLINE split #-}

join_ :: (Hashable i, Hashable f) => Expr i f -> Expr i f
join_ i = intern $ CEJoin i
{-# NOINLINE join_ #-}

bundle :: (Hashable i, Hashable f) => V.Vector (Expr i f) -> Expr i f
bundle i = intern $ CEBundle i
{-# NOINLINE bundle #-}
