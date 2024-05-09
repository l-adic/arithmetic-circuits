{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Circuit.Language.Expr
  ( Val (..),
    Var (..),
    UnOp (..),
    BinOp (..),
    Ty (..),
    Expr,
    evalExpr,
    rawWire,
    rawVal,
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
    rotate_,
    shift_,
    atIndex_,
    updateAtIndex_,
    reverse_,
    zeroBits_,
    Hash (..),
    Node (..),
    UBinOp (..),
    UUnOp (..),
    reifyGraph,
    BoolToField (..),
    relabelExpr,
    rotateList,
    shiftList,
  )
where

import Control.Exception (throw)
import Data.Field.Galois (GaloisField, Prime, PrimeField (fromP))
import Data.Finite (Finite)
import Data.Map qualified as Map
import Data.Semiring (Ring (..), Semiring (..))
import Data.Sequence ((|>), pattern Empty, pattern (:|>))
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.Sized qualified as SV
import GHC.TypeNats (Log2, type (+))
import Lens.Micro (ix, (.~))
import Numeric (showHex)
import Protolude hiding (Semiring (..))
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)

data Ty = TField | TBool | TVec Nat Ty

type family HType f (ty :: Ty) where
  HType f 'TField = f
  HType _ 'TBool = Bool
  HType f ('TVec n ty) = SV.Vector n (HType f ty)

data Val f (ty :: Ty) where
  ValField :: f -> Val f 'TField
  ValBool :: f -> Val f 'TBool

deriving instance (Eq f) => Eq (Val f ty)

deriving instance (Show f) => Show (Val f ty)

instance (Pretty f) => Pretty (Val f ty) where
  pretty (ValField f) = pretty f
  pretty (ValBool b) = pretty b

rawVal :: Val f ty -> f
rawVal (ValField f) = f
rawVal (ValBool f) = f
{-# INLINE rawVal #-}

data Var i f (ty :: Ty) where
  VarField :: i -> Var i f 'TField
  VarBool :: i -> Var i f 'TBool

deriving instance (Eq i) => Eq (Var i f ty)

deriving instance (Show i, Show f) => Show (Var i f ty)

instance (Pretty i) => Pretty (Var i f ty) where
  pretty (VarField f) = pretty f
  pretty (VarBool b) = pretty b

rawWire :: Var i f ty -> i
rawWire (VarField i) = i
rawWire (VarBool i) = i
{-# INLINE rawWire #-}

data UnOp f (ty :: Ty) where
  UNeg :: UnOp f 'TField
  UNegs :: UnOp f ('TVec n 'TField)
  UNot :: UnOp f 'TBool
  UNots :: UnOp f ('TVec n 'TBool)
  URot :: (KnownNat n) => Int -> UnOp f ('TVec n ty)
  UShift :: (KnownNat n) => Int -> UnOp f ('TVec n 'TBool)
  UReverse :: (KnownNat n) => UnOp f ('TVec n ty)

deriving instance (Show f) => Show (UnOp f a)

deriving instance Eq (UnOp f a)

instance Pretty (UnOp f a) where
  pretty op = case op of
    UNeg -> text "neg"
    UNegs -> text "negs"
    UNot -> text "!"
    UNots -> text "nots"
    URot n -> text "rotate" <+> pretty n
    UShift n -> text "shift" <+> pretty n
    UReverse -> text "reverse"

data BinOp f (a :: Ty) where
  BAdd :: BinOp f 'TField
  BAdds :: BinOp f (TVec n 'TField)
  BSub :: BinOp f 'TField
  BSubs :: BinOp f (TVec n 'TField)
  BMul :: BinOp f 'TField
  BMuls :: BinOp f (TVec n 'TField)
  BDiv :: BinOp f 'TField
  BDivs :: BinOp f (TVec n 'TField)
  BAnd :: BinOp f 'TBool
  BAnds :: BinOp f (TVec n 'TBool)
  BOr :: BinOp f 'TBool
  BOrs :: BinOp f (TVec n 'TBool)
  BXor :: BinOp f 'TBool
  BXors :: BinOp f (TVec n 'TBool)

deriving instance (Show f) => Show (BinOp f a)

deriving instance Eq (BinOp f a)

instance Pretty (BinOp f a) where
  pretty op = case op of
    BAdd -> text "+"
    BAdds -> text ".+."
    BSub -> text "-"
    BSubs -> text ".-."
    BMul -> text "*"
    BMuls -> text ".*."
    BDiv -> text "/"
    BDivs -> text "./."
    BAnd -> text "&&"
    BAnds -> text ".&&."
    BOr -> text "||"
    BOrs -> text ".||."
    BXor -> text "xor"
    BXors -> text "xors"

opPrecedence :: BinOp f a -> Int
opPrecedence BOr = 5
opPrecedence BOrs = 5
opPrecedence BXor = 5
opPrecedence BXors = 5
opPrecedence BAnd = 5
opPrecedence BAnds = 5
opPrecedence BSub = 6
opPrecedence BSubs = 6
opPrecedence BAdd = 6
opPrecedence BAdds = 6
opPrecedence BMul = 7
opPrecedence BMuls = 7
opPrecedence BDiv = 8
opPrecedence BDivs = 8

type family NBits a :: Nat where
  NBits (Prime p) = (Log2 p) + 1

newtype Hash = Hash Int
  deriving (Show, Eq, Ord)
  deriving (Hashable) via Int

instance Pretty Hash where
  pretty (Hash i) =
    let s = if i < 0 then "-" else ""
     in s <> "0x" <> pretty (take 7 $ showHex (abs i) "")

-- | Expression data type of (arithmetic) expressions over a field @f@
-- with variable names/indices coming from @i@.
data Expr i f (ty :: Ty) where
  EVal :: Hash -> Val f ty -> Expr i f ty
  EVar :: Hash -> Var i f ty -> Expr i f ty
  EUnOp :: Hash -> UnOp f ty -> Expr i f ty -> Expr i f ty
  EBinOp :: Hash -> BinOp f ty -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EIf :: Hash -> Expr i f 'TBool -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EEq :: Hash -> Expr i f 'TField -> Expr i f 'TField -> Expr i f 'TBool
  ESplit :: (KnownNat (NBits f)) => Hash -> Expr i f 'TField -> Expr i f ('TVec (NBits f) 'TBool)
  EJoin :: (KnownNat n) => Hash -> Expr i f ('TVec n 'TBool) -> Expr i f 'TField
  EBundle :: Hash -> SV.Vector n (Expr i f ty) -> Expr i f ('TVec n ty)
  EAtIndex :: (KnownNat n) => Hash -> Expr i f ('TVec n ty) -> Finite n -> Expr i f ty
  EUpdateAtIndex :: (KnownNat n) => Hash -> Expr i f ('TVec n ty) -> Finite n -> Expr i f ty -> Expr i f ('TVec n ty)

relabelExpr :: (i -> j) -> Expr i f ty -> Expr j f ty
relabelExpr _ (EVal h v) = EVal h v
relabelExpr f (EVar h v) = EVar h $ case v of
  VarField i -> VarField $ f i
  VarBool i -> VarBool $ f i
relabelExpr f (EUnOp h op e) = EUnOp h op $ relabelExpr f e
relabelExpr f (EBinOp h op e1 e2) = EBinOp h op (relabelExpr f e1) (relabelExpr f e2)
relabelExpr f (EIf h b t e) = EIf h (relabelExpr f b) (relabelExpr f t) (relabelExpr f e)
relabelExpr f (EEq h l r) = EEq h (relabelExpr f l) (relabelExpr f r)
relabelExpr f (ESplit h i) = ESplit h $ relabelExpr f i
relabelExpr f (EJoin h i) = EJoin h $ relabelExpr f i
relabelExpr f (EBundle h b) = EBundle h $ relabelExpr f <$> b
relabelExpr f (EAtIndex h e i) = EAtIndex h (relabelExpr f e) i
relabelExpr f (EUpdateAtIndex h e i v) = EUpdateAtIndex h (relabelExpr f e) i (relabelExpr f v)

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
getId (EAtIndex i _ _) = i
getId (EUpdateAtIndex i _ _ _) = i
{-# INLINE getId #-}

instance Eq (Expr i f ty) where
  a == b = getId a == getId b

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
          EAtIndex _ a i -> pretty a <+> text "!" <> pretty (toInteger i)
          EUpdateAtIndex _ a i v -> pretty a <+> text "!" <> pretty (toInteger i) <+> text ":=" <+> pretty v

parensPrec :: Int -> Int -> Doc -> Doc
parensPrec opPrec p = if p > opPrec then parens else identity

--------------------------------------------------------------------------------

-- | Evaluate arithmetic expressions directly, given an environment
evalExpr ::
  forall i f vars ty.
  (PrimeField f) =>
  -- | lookup function for variable mapping
  (i -> vars -> Maybe f) ->
  -- | variables
  vars ->
  -- | circuit to evaluate
  Expr i f ty ->
  Either (EvalError i) (V.Vector f)
evalExpr lookupVar vars expr =
  evalState (runExceptT (evalGraph lookupVar vars (reifyGraph expr))) mempty

rotateList :: Int -> [a] -> [a]
rotateList steps x
  | steps == 0 = x
  | otherwise = take l $ drop n $ cycle x
  where
    l = length x
    n = l - (steps `mod` l)

shiftList :: a -> Int -> [a] -> [a]
shiftList def n xs
  | n == 0 = xs
  | abs n >= length xs = replicate (length xs) def
  | n < 0 = drop (abs n) xs <> replicate (abs n) def
  | otherwise =
      let (as, _) = splitAt (length xs - n) xs
       in replicate (abs n) def <> as

instance (Hashable f, Hashable i, Num f) => Semiring (Expr i f 'TField) where
  plus = binOp_ BAdd
  zero = val_ (ValField 0)
  times = binOp_ BMul
  one = val_ (ValField 1)

instance (Num f, Hashable i, Hashable f) => Ring (Expr i f 'TField) where
  negate = unOp_ UNeg

instance (Num f, Hashable i, Hashable f) => Num (Expr i f 'TField) where
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
{-# INLINE val_ #-}

var_ ::
  forall i f ty.
  (Hashable i) =>
  (Hashable f) =>
  Var i f ty ->
  Expr i f ty
var_ v =
  let h = Hash $ hash (NVar (rawWire v) :: Node i f)
   in EVar h v
{-# INLINE var_ #-}

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
{-# INLINE unOp_ #-}

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
{-# INLINE binOp_ #-}

if_ ::
  forall i f a.
  (Hashable i) =>
  (Hashable f) =>
  Expr i f 'TBool ->
  Expr i f a ->
  Expr i f a ->
  Expr i f a
if_ b t f =
  let h = Hash $ hash (NIf (getId b) (getId t) (getId f) :: Node i f)
   in EIf h b t f
{-# INLINE if_ #-}

eq_ ::
  forall i f.
  (Hashable i) =>
  (Hashable f) =>
  Expr i f 'TField ->
  Expr i f 'TField ->
  Expr i f 'TBool
eq_ l r =
  let h = Hash $ hash (NEq (getId l) (getId r) :: Node i f)
   in EEq h l r
{-# INLINE eq_ #-}

split_ ::
  forall i f.
  (Hashable i) =>
  (Hashable f) =>
  (KnownNat (NBits f)) =>
  Expr i f 'TField ->
  Expr i f ('TVec (NBits f) 'TBool)
split_ i =
  let h = Hash $ hash (NSplit (getId i) (fromIntegral $ natVal (Proxy @(NBits f))) :: Node i f)
   in ESplit h i
{-# INLINE split_ #-}

join_ ::
  forall i f n.
  (Hashable i) =>
  (Hashable f) =>
  (KnownNat n) =>
  Expr i f ('TVec n 'TBool) ->
  Expr i f 'TField
join_ i =
  let h = Hash $ hash (NJoin (getId i) :: Node i f)
   in EJoin h i
{-# INLINE join_ #-}

bundle_ ::
  forall i f n ty.
  (Hashable f) =>
  (Hashable i) =>
  SV.Vector n (Expr i f ty) ->
  Expr i f ('TVec n ty)
bundle_ b =
  let h = Hash $ hash (NBundle (getId <$> SV.fromSized b) :: Node i f)
   in EBundle h b
{-# INLINE bundle_ #-}

rotate_ ::
  forall i f n ty.
  (Hashable f) =>
  (Hashable i) =>
  (KnownNat n) =>
  Expr i f ('TVec n ty) ->
  Int ->
  Expr i f ('TVec n ty)
rotate_ e n = unOp_ (URot n) e
{-# INLINE rotate_ #-}

shift_ ::
  forall i f n.
  (Hashable f) =>
  (Hashable i) =>
  (KnownNat n) =>
  Expr i f ('TVec n 'TBool) ->
  Int ->
  Expr i f ('TVec n 'TBool)
shift_ e n = unOp_ (UShift n) e

atIndex_ ::
  forall i f n ty.
  (Hashable f) =>
  (Hashable i) =>
  (KnownNat n) =>
  Expr i f ('TVec n ty) ->
  Finite n ->
  Expr i f ty
atIndex_ e i =
  let h = Hash $ hash (NAtIndex (getId e) (fromIntegral i) :: Node i f)
   in EAtIndex h e i
{-# INLINE atIndex_ #-}

reverse_ ::
  forall i f n.
  (Hashable f) =>
  (Hashable i) =>
  (KnownNat n) =>
  Expr i f ('TVec n 'TBool) ->
  Expr i f ('TVec n 'TBool)
reverse_ = unOp_ UReverse

updateAtIndex_ ::
  forall i f n ty.
  (Hashable f) =>
  (Hashable i) =>
  (KnownNat n) =>
  Expr i f ('TVec n ty) ->
  Finite n ->
  Expr i f ty ->
  Expr i f ('TVec n ty)
updateAtIndex_ e i v =
  let h = Hash $ hash (NUpdateAtIndex (getId e) (fromIntegral i) (getId v) :: Node i f)
   in EUpdateAtIndex h e i v
{-# INLINE updateAtIndex_ #-}

class BoolToField b f where
  boolToField :: b -> f

instance (GaloisField f) => BoolToField Bool f where
  boolToField b = fromInteger $ if b then 1 else 0

instance BoolToField (Val f 'TBool) (Val f 'TField) where
  boolToField (ValBool b) = ValField b

instance BoolToField (Var i f 'TBool) (Var i f 'TField) where
  boolToField (VarBool i) = VarField i

instance BoolToField (Expr i f 'TBool) (Expr i f 'TField) where
  boolToField = unsafeCoerce

instance BoolToField (Expr i f ('TVec n 'TBool)) (Expr i f ('TVec n 'TField)) where
  boolToField = unsafeCoerce

zeroBits_ :: forall n i f. (KnownNat n, Hashable i, Hashable f, GaloisField f) => Expr i f ('TVec n 'TBool)
zeroBits_ = bundle_ $ SV.replicate @n (val_ $ ValBool 0)

instance (KnownNat n, Hashable i, Hashable f, GaloisField f) => Bits (Expr i f ('TVec n 'TBool)) where
  (.&.) = binOp_ BAnds
  (.|.) = binOp_ BOrs
  xor = binOp_ BXors
  complement = unOp_ UNots
  shift e n = shift_ e n
  rotate e n = rotate_ e n
  bitSizeMaybe _ = Just $ fromIntegral $ natVal (Proxy @n)
  bitSize _ = fromIntegral $ natVal (Proxy @n)
  isSigned _ = False
  bit i
    | i < 0 || i >= fromIntegral (natVal (Proxy @n)) = throw Overflow
    | otherwise = updateAtIndex_ zeroBits_ (fromIntegral i) (val_ $ ValBool 1)
  setBit a i
    | i < 0 || i >= fromIntegral (natVal (Proxy @n)) = throw Overflow
    | otherwise = updateAtIndex_ a (fromIntegral i) (val_ $ ValBool 1)
  clearBit a i
    | i < 0 || i >= fromIntegral (natVal (Proxy @n)) = throw Overflow
    | otherwise = updateAtIndex_ a (fromIntegral i) (val_ $ ValBool 0)
  testBit _ _ = panic "testBit not implemented"
  popCount = panic "popCount not implemented"

instance (KnownNat n, Hashable i, Hashable f, GaloisField f) => FiniteBits (Expr i f ('TVec n 'TBool)) where
  finiteBitSize _ = fromIntegral $ natVal (Proxy @n)

-------------------------------------------------------------------------------

data UBinOp
  = UBAdd
  | UBSub
  | UBMul
  | UBDiv
  | UBAnd
  | UBOr
  | UBXor
  deriving (Show, Eq, Generic)

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

data UUnOp = UUNeg | UUNot | UURot Int | UUShift Int | UUReverse deriving (Show, Eq, Generic)

instance Hashable UUnOp

instance Pretty UUnOp where
  pretty op = case op of
    UUNeg -> text "neg"
    UUNot -> text "!"
    UURot n -> text "rotate" <+> pretty n
    UUShift n -> text "shift" <+> pretty n
    UUReverse -> text "reverse"

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
  NAtIndex :: Hash -> Int -> Node i f
  NUpdateAtIndex :: Hash -> Int -> Hash -> Node i f

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
  pretty (NAtIndex e idx) = pretty e <+> "!" <> pretty idx
  pretty (NUpdateAtIndex e idx v) = pretty e <+> "!" <> pretty idx <+> ":=" <+> pretty v

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
  hashWithSalt s (NAtIndex e idx) = s `hashWithSalt` ("NAtIndex" :: Text) `hashWithSalt` e `hashWithSalt` idx
  hashWithSalt s (NUpdateAtIndex e idx v) = s `hashWithSalt` ("NUpdateAtIndex" :: Text) `hashWithSalt` e `hashWithSalt` idx `hashWithSalt` v

untypeUnOp :: UnOp f a -> UUnOp
untypeUnOp UNeg = UUNeg
untypeUnOp UNegs = UUNeg
untypeUnOp UNot = UUNot
untypeUnOp UNots = UUNot
untypeUnOp (URot n) = UURot n
untypeUnOp (UShift n) = UUShift n
untypeUnOp UReverse = UUReverse
{-# INLINE untypeUnOp #-}

untypeBinOp :: BinOp f a -> UBinOp
untypeBinOp BAdd = UBAdd
untypeBinOp BAdds = UBAdd
untypeBinOp BSub = UBSub
untypeBinOp BSubs = UBSub
untypeBinOp BMul = UBMul
untypeBinOp BMuls = UBMul
untypeBinOp BDiv = UBDiv
untypeBinOp BDivs = UBDiv
untypeBinOp BAnd = UBAnd
untypeBinOp BAnds = UBAnd
untypeBinOp BOr = UBOr
untypeBinOp BOrs = UBOr
untypeBinOp BXor = UBXor
untypeBinOp BXors = UBXor
{-# INLINE untypeBinOp #-}

--------------------------------------------------------------------------------

reifyGraph :: Expr i f ty -> Seq (Hash, Node i f)
reifyGraph e =
  gbsEdges $ execState (buildGraph_ e) (GraphBuilderState mempty mempty)

data GraphBuilderState i f = GraphBuilderState
  { gbsSharedNodes :: Set Hash,
    gbsEdges :: Seq (Hash, Node i f)
  }

{-# SCC buildGraph_ #-}
buildGraph_ :: forall i f ty. Expr i f ty -> State (GraphBuilderState i f) Hash
buildGraph_ expr =
  getId expr <$ case expr of
    EVal h v -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        let n = NVal (rawVal v)
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns,
              gbsEdges = gbsEdges s |> (h, n)
            }
    EVar h v -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        let n = NVar (rawWire v)
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns,
              gbsEdges = gbsEdges s |> (h, n)
            }
    EUnOp h op e -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        e' <- buildGraph_ e
        let n = NUnOp (untypeUnOp op) e'
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    EBinOp h op e1 e2 -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        e1' <- buildGraph_ e1
        e2' <- buildGraph_ e2
        let n = NBinOp (untypeBinOp op) e1' e2'
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    EIf h b t f -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        b' <- buildGraph_ b
        t' <- buildGraph_ t
        f' <- buildGraph_ f
        let n = NIf b' t' f'
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    EEq h l r -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        l' <- buildGraph_ l
        r' <- buildGraph_ r
        let n = NEq l' r'
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    ESplit h i -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        i' <- buildGraph_ i
        let n = NSplit i' (fromIntegral $ natVal (Proxy @(NBits f)))
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    EJoin h i -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        i' <- buildGraph_ i
        let n = NJoin i'
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    EBundle h b -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        b' <- SV.fromSized <$> traverse buildGraph_ b
        let n = NBundle b'
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    EAtIndex h e i -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        e' <- buildGraph_ e
        let n = NAtIndex e' (fromIntegral i)
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }
    EUpdateAtIndex h e i v -> do
      ns <- gets gbsSharedNodes
      unless (h `Set.member` ns) $ do
        modify $ \s ->
          s
            { gbsSharedNodes = Set.insert h ns
            }
        e' <- buildGraph_ e
        v' <- buildGraph_ v
        let n = NUpdateAtIndex e' (fromIntegral i) v'
        modify $ \s ->
          s
            { gbsEdges = gbsEdges s |> (h, n)
            }

--------------------------------------------------------------------------------

data EvalError i
  = MissingVar i
  | TypeErr Text
  | MissingFromCache Hash
  deriving (Show, Eq)

type EvalM i f = ExceptT (EvalError i) (State (Map Hash (V.Vector f)))

evalGraph ::
  forall i f vars.
  (PrimeField f) =>
  -- | lookup function for variable mapping
  (i -> vars -> Maybe f) ->
  -- | variables
  vars ->
  -- | circuit to evaluate
  Seq (Hash, Node i f) ->
  EvalM i f (V.Vector f)
evalGraph lookupVar vars graph = case graph of
  Empty -> panic "empty graph"
  ns :|> n -> traverse eval ns >> eval n
  where
    eval (h, n) = evalNode lookupVar vars h n

evalNode ::
  (PrimeField f) =>
  (i -> vars -> Maybe f) ->
  -- | variables
  vars ->
  -- | circuit to evaluate
  Hash ->
  Node i f ->
  EvalM i f (V.Vector f)
evalNode lookupVar vars h node =
  case node of
    NVal f -> cachResult h (V.singleton f)
    NVar i -> case lookupVar i vars of
      Just v -> cachResult h (V.singleton v)
      Nothing -> throwError $ MissingVar i
    NUnOp op e -> do
      e' <- assertFromCache e
      res <- case op of
        UUNeg -> pure $ fmap Protolude.negate $ e'
        UUNot -> pure $ fmap (\x -> 1 - x) $ e'
        UURot n ->
          pure $ V.fromList . rotateList n $ V.toList e'
        UUShift n ->
          pure $ V.fromList . shiftList 0 n $ V.toList e'
        UUReverse ->
          pure $ V.reverse e'
      cachResult h res
    NBinOp op e1 e2 -> do
      e1' <- assertFromCache e1
      e2' <- assertFromCache e2
      assertSameLength e1' e2'
      let apply = case op of
            UBAdd -> (+)
            UBSub -> (-)
            UBMul -> (*)
            UBDiv -> (/)
            UBAnd -> \x y -> if x == 1 && y == 1 then 1 else 0
            UBOr -> \x y -> if x == 1 || y == 1 then 1 else 0
            UBXor -> \x y -> if x /= y then 1 else 0
      let res = V.zipWith apply e1' e2'
      cachResult h res
    NIf b t f -> do
      b' <- assertField =<< assertFromCache b
      t' <- assertFromCache t
      f' <- assertFromCache f
      let res = if b' == 1 then t' else f'
      cachResult h res
    NEq l r -> do
      l' <- assertFromCache l
      r' <- assertFromCache r
      res <- do
        isEq <- (==) <$> assertField l' <*> assertField r'
        pure . V.singleton $ if isEq then 1 else 0
      cachResult h res
    NSplit e n -> do
      e' <- assertField =<< assertFromCache e
      let res = V.generate n $ \_ix -> boolToField $ testBit (fromP e') (fromIntegral _ix)
      cachResult h res
    NJoin e -> do
      e' <- assertFromCache e
      let res = V.singleton $ V.ifoldl' (\acc i b -> acc + if b == 1 then 2 ^ i else 0) 0 e'
      cachResult h res
    NBundle es -> do
      res <- for es $ \e ->
        assertFromCache e >>= assertField
      cachResult h res
    NAtIndex e idx -> do
      e' <- assertFromCache e
      let res = e' V.! idx
      cachResult h $ V.singleton res
    NUpdateAtIndex e idx v -> do
      e' <- toList <$> assertFromCache e
      v' <- assertField =<< assertFromCache v
      let res = V.fromList $ e' & ix idx .~ v'
      cachResult h res
  where
    cachResult i v = v <$ modify (Map.insert i v)
    {-# INLINE cachResult #-}

    assertSameLength x y = do
      when (V.length x /= V.length y) $ throwError $ TypeErr "vectors must have the same length"
    {-# INLINE assertSameLength #-}

    assertField :: V.Vector f -> EvalM i f f
    assertField x
      | V.length x == 1 = pure $ V.head x
      | otherwise = throwError $ TypeErr "expected field, got vector"

    assertFromCache :: Hash -> EvalM i f (V.Vector f)
    assertFromCache i = do
      m <- get
      case Map.lookup i m of
        Just ws -> pure ws
        Nothing -> throwError $ MissingFromCache i
    {-# INLINE assertFromCache #-}
