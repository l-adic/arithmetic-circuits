{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Circuit.Language.TExpr
  ( Val (..),
    Var (..),
    UnOp (..),
    BinOp (..),
    Expr,
    evalExpr,
    rawWire,
    rawVal,
    Ground (..),
    type NBits,
    getId,
    val_,
    var_,
    unOp_,
    binOp_,
    if_,
    eq_,
    split_,
    join_,
    bundle_,
    Hash (..),
    Node (..),
    UBinOp (..),
    UUnOp (..),
    reifyGraph,
  )
where

import Control.Monad.Cont (ContT (runContT))
import Data.Field.Galois (PrimeField (fromP))
import Data.Graph (graphFromEdges, reverseTopSort)
import Data.Map qualified as Map
import Data.Semiring (Ring (..), Semiring (..))
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.Sized qualified as SV
import Numeric (showHex)
import Protolude hiding (Semiring (..))
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)

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

data UnOp f a where
  UNeg :: UnOp f f
  UNot :: UnOp f Bool

deriving instance (Show f) => Show (UnOp f a)

deriving instance Eq (UnOp f a)

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

deriving instance Eq (BinOp f a)

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

newtype Hash = Hash Int
  deriving (Show, Eq, Ord)
  deriving (Hashable) via Int

instance Pretty Hash where
  pretty (Hash i) =
    let s = if i < 0 then "-" else ""
     in s <> "0x" <> pretty (take 7 $ showHex (abs i) "")

-- | Expression data type of (arithmetic) expressions over a field @f@
-- with variable names/indices coming from @i@.
data Expr i f ty where
  EVal :: Hash -> Val f ty -> Expr i f ty
  EVar :: Hash -> Var i f ty -> Expr i f ty
  EUnOp :: Hash -> UnOp f ty -> Expr i f ty -> Expr i f ty
  EBinOp :: Hash -> BinOp f ty -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EIf :: Hash -> Expr i f Bool -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EEq :: Hash -> Expr i f f -> Expr i f f -> Expr i f Bool
  ESplit :: (KnownNat (NBits f)) => Hash -> Expr i f f -> Expr i f (SV.Vector (NBits f) Bool)
  EJoin :: (KnownNat n) => Hash -> Expr i f (SV.Vector n Bool) -> Expr i f f
  EBundle :: Hash -> SV.Vector n (Expr i f ty) -> Expr i f (SV.Vector n ty)

deriving instance (Show i, Show f) => Show (Expr i f ty)

getId :: Expr i f ty -> Hash
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

instance (Hashable f, Hashable i, Num f) => Semiring (Expr i f f) where
  plus = binOp_ BAdd
  zero = val_ (ValField 0)
  times = binOp_ BMul
  one = val_ (ValField 1)

instance (Num f, Hashable i, Hashable f) => Ring (Expr i f f) where
  negate = unOp_ UNeg

instance (Num f, Hashable i, Hashable f) => Num (Expr i f f) where
  (+) = plus
  (*) = times
  (-) = binOp_ BSub
  negate = unOp_ UNeg
  abs = identity
  signum = const 1
  fromInteger = val_ . ValField . fromInteger

val_ ::
  forall i f ty.
  (Hashable i) =>
  (Hashable f) =>
  Val f ty ->
  Expr i f ty
val_ v =
  let h = Hash $ hash $ (NVal (rawVal v) :: Node i f)
   in EVal h v

var_ ::
  forall i f ty.
  (Hashable i) =>
  (Hashable f) =>
  Var i f ty ->
  Expr i f ty
var_ v =
  let h = Hash $ hash (NVar (rawWire v) :: Node i f)
   in EVar h v

unOp_ ::
  forall i f a.
  (Hashable i) =>
  (Hashable f) =>
  UnOp f a ->
  Expr i f a ->
  Expr i f a
unOp_ op e =
  let h = Hash $ hash $ (NUnOp (untypeUnOp op) (getId e) :: Node i f)
   in EUnOp h op e

binOp_ ::
  forall i f a.
  (Hashable i) =>
  (Hashable f) =>
  BinOp f a ->
  Expr i f a ->
  Expr i f a ->
  Expr i f a
binOp_ op e1 e2 =
  let h = Hash $ hash $ (NBinOp (untypeBinOp op) (getId e1) (getId e2) :: Node i f)
   in EBinOp h op e1 e2

if_ ::
  forall i f a.
  (Hashable i) =>
  (Hashable f) =>
  Expr i f Bool ->
  Expr i f a ->
  Expr i f a ->
  Expr i f a
if_ b t f =
  let h = Hash $ hash (NIf (getId b) (getId t) (getId f) :: Node i f)
   in EIf h b t f

eq_ ::
  forall i f.
  (Hashable i) =>
  (Hashable f) =>
  Expr i f f ->
  Expr i f f ->
  Expr i f Bool
eq_ l r =
  let h = Hash $ hash (NEq (getId l) (getId r) :: Node i f)
   in EEq h l r

split_ ::
  forall i f.
  (Hashable i) =>
  (Hashable f) =>
  (KnownNat (NBits f)) =>
  Expr i f f ->
  Expr i f (SV.Vector (NBits f) Bool)
split_ i =
  let h = Hash $ hash (NSplit (getId i) (fromIntegral $ natVal (Proxy @(NBits f))) :: Node i f)
   in ESplit h i

join_ ::
  forall i f n.
  (Hashable i) =>
  (Hashable f) =>
  (KnownNat n) =>
  Expr i f (SV.Vector n Bool) ->
  Expr i f f
join_ i =
  let h = Hash $ hash (NJoin (getId i) :: Node i f)
   in EJoin h i

bundle_ ::
  forall i f n ty.
  (Hashable f) =>
  (Hashable i) =>
  SV.Vector n (Expr i f ty) ->
  Expr i f (SV.Vector n ty)
bundle_ b =
  let h = Hash $ hash (NBundle (getId <$> SV.fromSized b) :: Node i f)
   in EBundle h b

--------------------------------------------------------------------------------

data UBinOp = UBAdd | UBSub | UBMul | UBDiv | UBAnd | UBOr | UBXor deriving (Show, Eq, Generic)

instance Hashable UBinOp

instance Pretty UBinOp where
  pretty op = case op of
    UBAdd -> text "+"
    UBSub -> text "-"
    UBMul -> text "*"
    UBDiv -> text "/"
    UBAnd -> text "&&"
    UBOr -> text "||"
    UBXor -> text "xor"

data UUnOp = UUNeg | UUNot deriving (Show, Eq, Generic)

instance Hashable UUnOp

instance Pretty UUnOp where
  pretty op = case op of
    UUNeg -> text "neg"
    UUNot -> text "!"

data Node i f where
  NVal :: f -> Node i f
  NVar :: i -> Node i f
  NUnOp :: UUnOp -> Hash -> Node i f
  NBinOp :: UBinOp -> Hash -> Hash -> Node i f
  NIf :: Hash -> Hash -> Hash -> Node i f
  NEq :: Hash -> Hash -> Node i f
  NSplit :: Hash -> Int -> Node i f
  NJoin :: Hash -> Node i f
  NBundle :: V.Vector Hash -> Node i f

instance (Pretty f, Pretty i) => Pretty (Node i f) where
  pretty (NVal f) = pretty f
  pretty (NVar i) = "Var" <+> pretty i
  pretty (NUnOp op e) = pretty op <+> pretty e
  pretty (NBinOp op e1 e2) = pretty e1 <+> pretty op <+> pretty e2
  pretty (NIf b t f) = "if" <+> pretty b <+> "then" <+> pretty t <+> "else" <+> pretty f
  pretty (NEq l r) = pretty l <+> "==" <+> pretty r
  pretty (NSplit e n) = "split" <+> pretty e <+> pretty n
  pretty (NJoin e) = "join" <+> pretty e
  pretty (NBundle es) = "bundle" <+> pretty (toList es)

deriving instance (Show i, Show f) => Show (Node i f)

deriving instance (Eq i, Eq f) => Eq (Node i f)

instance (Hashable i, Hashable f) => Hashable (Node i f) where
  hashWithSalt s (NVal f) = s `hashWithSalt` ("NVal" :: Text) `hashWithSalt` f
  hashWithSalt s (NVar i) = s `hashWithSalt` ("NVar" :: Text) `hashWithSalt` i
  hashWithSalt s (NUnOp op e) = s `hashWithSalt` ("NUnOp" :: Text) `hashWithSalt` op `hashWithSalt` e
  hashWithSalt s (NBinOp op e1 e2) = s `hashWithSalt` ("NBinOp" :: Text) `hashWithSalt` op `hashWithSalt` e1 `hashWithSalt` e2
  hashWithSalt s (NIf b t f) = s `hashWithSalt` ("NIf" :: Text) `hashWithSalt` b `hashWithSalt` t `hashWithSalt` f
  hashWithSalt s (NEq l r) = s `hashWithSalt` ("NEq" :: Text) `hashWithSalt` l `hashWithSalt` r
  hashWithSalt s (NSplit e n) = s `hashWithSalt` ("NSplit" :: Text) `hashWithSalt` e `hashWithSalt` n
  hashWithSalt s (NJoin e) = s `hashWithSalt` ("NJoin" :: Text) `hashWithSalt` e
  hashWithSalt s (NBundle es) = s `hashWithSalt` ("NBundle" :: Text) `hashWithSalt` toList es

untypeUnOp :: UnOp f a -> UUnOp
untypeUnOp UNeg = UUNeg
untypeUnOp UNot = UUNot

untypeBinOp :: BinOp f a -> UBinOp
untypeBinOp BAdd = UBAdd
untypeBinOp BSub = UBSub
untypeBinOp BMul = UBMul
untypeBinOp BDiv = UBDiv
untypeBinOp BAnd = UBAnd
untypeBinOp BOr = UBOr
untypeBinOp BXor = UBXor

reifyGraph :: Expr i f ty -> [(Hash, Node i f)]
reifyGraph e =
  let h (a, b, _) = (b, a)
   in h . f <$> reverseTopSort g
  where
    (g, f, _) = graphFromEdges $ gbsEdges $ execState (runContT (buildGraph_ e) pure) (GraphBuilderState mempty mempty)

data GraphBuilderState i f = GraphBuilderState
  { gbsSharedNodes :: Set Hash,
    gbsEdges :: [(Node i f, Hash, [Hash])]
  }

buildGraph_ :: forall i f r ty. Expr i f ty -> ContT r (State (GraphBuilderState i f)) ()
buildGraph_ = \case
  EVal h v -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      let n = NVal (rawVal v)
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns,
            gbsEdges = (n, h, []) : gbsEdges s
          }
  EVar h v -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      let n = NVar (rawWire v)
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns,
            gbsEdges = (n, h, []) : gbsEdges s
          }
  EUnOp h op e -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns
          }
      buildGraph_ e
      let n = NUnOp (untypeUnOp op) (getId e)
      modify $ \s ->
        s
          { gbsEdges = (n, h, [getId e]) : gbsEdges s
          }
  EBinOp h op e1 e2 -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns
          }
      buildGraph_ e1
      buildGraph_ e2
      let n = NBinOp (untypeBinOp op) (getId e1) (getId e2)
      modify $ \s ->
        s
          { gbsEdges = (n, h, [getId e1, getId e2]) : gbsEdges s
          }
  EIf h b t f -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns
          }
      buildGraph_ b
      buildGraph_ t
      buildGraph_ f
      let n = NIf (getId b) (getId t) (getId f)
      modify $ \s ->
        s
          { gbsEdges = (n, h, [getId b, getId t, getId f]) : gbsEdges s
          }
  EEq h l r -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns
          }
      buildGraph_ l
      buildGraph_ r
      let n = NEq (getId l) (getId r)
      modify $ \s ->
        s
          { gbsEdges = (n, h, [getId l, getId r]) : gbsEdges s
          }
  ESplit h i -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns
          }
      buildGraph_ i
      let n = NSplit (getId i) (fromIntegral $ natVal (Proxy @(NBits f)))
      modify $ \s ->
        s
          { gbsEdges = (n, h, [getId i]) : gbsEdges s
          }
  EJoin h i -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns
          }
      buildGraph_ i
      let n = NJoin (getId i)
      modify $ \s ->
        s
          { gbsEdges = (n, h, [getId i]) : gbsEdges s
          }
  EBundle h b -> do
    ns <- gets gbsSharedNodes
    unless (h `Set.member` ns) $ do
      modify $ \s ->
        s
          { gbsSharedNodes = Set.insert h ns
          }
      traverse_ buildGraph_ b
      let n = NBundle (getId <$> SV.fromSized b)
      modify $ \s ->
        s
          { gbsEdges = (n, h, getId <$> toList b) : gbsEdges s
          }
