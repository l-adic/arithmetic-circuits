{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use zipWithM" #-}

module Circuit.Expr
  ( UnOp (..),
    BinOp (..),
    Val (..),
    Var (..),
    Expr (..),
    ExprM,
    BuilderState (..),
    type NBits,
    Ground(..),
    memoizedCompile,
    emit,
    imm,
    addVar,
    addWire,
    freshPublicInput,
    freshPrivateInput,
    freshOutput,
    rotateList,
    runCircuitBuilder,
    evalCircuitBuilder,
    execCircuitBuilder,
    truncRotate,
    evalExpr,
    rawWire,
    compileWithWires,
    compileWithWire,
    exprToArithCircuit,
  )
where

import Circuit.Affine
import Circuit.Arithmetic
import Data.Field.Galois (GaloisField, PrimeField (fromP))
import Data.Finite (Finite)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Data.Reify
import Data.Semiring (Ring (..), Semiring (..))
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.Sized qualified as SV
import Lens.Micro ((.~))
import Protolude hiding (Semiring)
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)
import Data.Interned
import Data.Hashable
import GHC.Conc.Sync (ThreadId(ThreadId))


data UnOp f a where
  UNeg :: UnOp f f
  UNot :: UnOp f Bool

-- \| # truncate bits, # rotate bits

data BinOp f a where
  BAdd :: BinOp f f
  BSub :: BinOp f f
  BMul :: BinOp f f
  BDiv :: BinOp f f
  BAnd :: BinOp f Bool
  BOr :: BinOp f Bool
  BXor :: BinOp f Bool

opPrecedence :: BinOp f a -> Int
opPrecedence BOr = 5
opPrecedence BXor = 5
opPrecedence BAnd = 5
opPrecedence BSub = 6
opPrecedence BAdd = 6
opPrecedence BMul = 7
opPrecedence BDiv = 8

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

newtype UVar i = UVar i deriving (Show, Eq, Generic)

instance Hashable i => Hashable (UVar i)

instance (Pretty i) => Pretty (UVar i) where
  pretty (UVar i) = "Var" <+> pretty i

type family NBits a :: Nat

-- | This constring prevents us from building up nested vectors inside the expression type
class Ground (t :: Type -> Type) (ty :: Type) (f :: Type) where
  coerceGroundType :: t ty  -> t f

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


--------------------------------------------------------------------------------

data UBinOp = UAdd | USub | UMul | UDiv | UAnd | UOr | UXor deriving (Show, Eq, Generic)

instance Hashable UBinOp

untypeBinOp :: BinOp f a -> UBinOp
untypeBinOp = \case
  BAdd -> UAdd
  BSub -> USub
  BMul -> UMul
  BDiv -> UDiv
  BAnd -> UAnd
  BOr -> UOr
  BXor -> UXor

data UUnOp = UUNeg | UUNot deriving (Show,Eq, Generic)

instance Hashable UUnOp

instance Pretty UBinOp where
  pretty = \case
    UAdd -> "+"
    USub -> "-"
    UMul -> "*"
    UDiv -> "/"
    UAnd -> "&&"
    UOr -> "||"
    UXor -> "xor"

instance Pretty UUnOp where
  pretty = \case
    UUNeg -> "-"
    UUNot -> "!"

untypeUnOp :: UnOp f a -> UUnOp
untypeUnOp = \case
  UNeg -> UUNeg
  UNot -> UUNot

data UntypedExpr a i f
  = UEVal a f
  | UEVar a (UVar i)
  | UEUnOp a UUnOp (UntypedExpr a i f)
  | UEBinOp a UBinOp (UntypedExpr a i f) (UntypedExpr a i f)
  | UEIf a (UntypedExpr a i f) (UntypedExpr a i f) (UntypedExpr a i f)
  | UEEq a (UntypedExpr a i f) (UntypedExpr a i f)
  | UESplit a Int (UntypedExpr a i f)
  | UEJoin a (UntypedExpr a i f)
  | UEAtIndex a (UntypedExpr a i f) Int
  | UEUpdateIndex a Int (UntypedExpr a i f) (UntypedExpr a i f)
  | UEBundle a (V.Vector (UntypedExpr a i f))
  deriving (Eq, Show)

data SharedUntypedExpr i f
  = SUEVal Id f
  | SUEVar Id (UVar i)
  | SUEUnOp Id UUnOp (SharedUntypedExpr i f)
  | SUEBinOp Id UBinOp (SharedUntypedExpr i f) (SharedUntypedExpr i f)
  | SUEIf Id (SharedUntypedExpr i f) (SharedUntypedExpr i f) (SharedUntypedExpr i f)
  | SUEEq Id (SharedUntypedExpr i f) (SharedUntypedExpr i f)
  | SUESplit Id Int (SharedUntypedExpr i f)
  | SUEJoin Id (SharedUntypedExpr i f)
  | SUEAtIndex Id (SharedUntypedExpr i f) Int
  | SUEUpdateIndex Id Int (SharedUntypedExpr i f) (SharedUntypedExpr i f)
  | SUEBundle Id !(V.Vector (SharedUntypedExpr i f))
  deriving (Eq, Show)

instance (Pretty i, Pretty f) => Pretty (SharedUntypedExpr i f) where
  pretty = \case
    SUEVal i f -> "Id" <+> pretty i <+> text ":" <+> parens (pretty f)
    SUEVar i v -> "Id" <+> pretty i <+> text ":" <+> pretty v
    SUEUnOp i op e -> "Id" <+> pretty i <+> text ":" <+> parens (pretty op <+> pretty e)
    SUEBinOp i op e1 e2 -> "Id" <+> pretty i <+> text ":" <+> parens (pretty op <+> pretty e1 <+> pretty e2)
    SUEIf i b t e -> "Id" <+> pretty i <+> text ":" <+> parens (text "if" <+> pretty b <+> text "then" <+> pretty t <+> text "else" <+> pretty e)
    SUEEq i l r -> "Id" <+> pretty i <+> text ":" <+> parens (pretty l <+> text "=" <+> pretty r)
    SUESplit i n e -> "Id" <+> pretty i <+> text ":" <+> parens (text "split" <+> pretty n <+> pretty e)
    SUEJoin i e -> "Id" <+> pretty i <+> text ":" <+> parens (text "join" <+> pretty e)
    SUEAtIndex i v ix -> "Id" <+> pretty i <+> text ":" <+> parens (pretty v <+> brackets (pretty ix))
    SUEUpdateIndex i p b v -> "Id" <+> pretty i <+> text ":" <+> parens (text ("setIndex " <> Protolude.show p) <+> pretty b <+> pretty v)
    SUEBundle i b -> "Id" <+> pretty i <+> text ":" <+> parens (text "bundle" <+> pretty (toList b))




unType :: forall f i ty. Expr i f ty -> UntypedExpr () i f
unType = \case
  EVal v -> case v of
    ValBool b -> UEVal () b
    ValField f -> UEVal () f
  EVar v -> UEVar () (UVar $ rawWire v)
  EUnOp op e -> UEUnOp () (untypeUnOp op) (unType e)
  EBinOp op e1 e2 -> UEBinOp () (untypeBinOp op) (unType e1) (unType e2)
  EIf b t e -> UEIf () (unType b) (unType t) (unType e)
  EEq l r -> UEEq () (unType l) (unType r)
  ESplit i -> UESplit () (fromIntegral $ natVal (Proxy @(NBits f))) (unType i)
  EJoin i -> UEJoin () (unType i)
  EAtIndex v ix -> UEAtIndex () (unType v) (fromIntegral ix)
  EUpdateIndex p b v -> UEUpdateIndex () (fromIntegral p) (unType b) (unType v)
  EBundle b -> UEBundle () (unType <$> SV.fromSized b)

getAnnotation :: UntypedExpr a i f -> a
getAnnotation = \case
  UEVal a _ -> a
  UEVar a _ -> a
  UEUnOp a _ _ -> a
  UEBinOp a _ _ _ -> a
  UEIf a _ _ _ -> a
  UEEq a _ _ -> a
  UESplit a _ _ -> a
  UEJoin a _ -> a
  UEAtIndex a _ _ -> a
  UEUpdateIndex a _ _ _ -> a
  UEBundle a _ -> a

hashCons :: (Hashable i, Hashable f) => UntypedExpr () i f -> UntypedExpr Int i f
hashCons = \case 
  UEVal _ f -> UEVal (hash (hash @Text "Val", f)) f
  UEVar _ v -> UEVar (hash (hash @Text "Var", v)) v
  UEUnOp _ op e -> 
    let e' = hashCons e
    in UEUnOp (hash (op, getAnnotation e')) op e'
  UEBinOp _ op e1 e2 ->
    let e1' = hashCons e1
        e2' = hashCons e2
    in UEBinOp (hash (op, getAnnotation e1', getAnnotation e2')) op e1' e2'
  UEIf _ b t e ->
    let b' = hashCons b
        t' = hashCons t
        e' = hashCons e
    in UEIf (hash (hash @Text "If", getAnnotation b', getAnnotation t', getAnnotation e')) b' t' e'
  UEEq _ l r ->
    let l' = hashCons l
        r' = hashCons r
    in UEEq (hash (hash @Text "Eq", getAnnotation l', getAnnotation r')) l' r'
  UESplit _ n e ->
    let e' = hashCons e
    in UESplit (hash (hash @Text "Split", n, getAnnotation e')) n e'
  UEJoin _ e ->
    let e' = hashCons e
    in UEJoin (hash (hash @Text "Join", getAnnotation e')) e'
  UEAtIndex _ v ix ->
    let v' = hashCons v
    in UEAtIndex (hash (hash @Text "AtIndex", getAnnotation v', ix)) v' ix
  UEUpdateIndex _ p b v ->
    let b' = hashCons b
        v' = hashCons v
    in UEUpdateIndex (hash (hash @Text "UpdateIndex", p, getAnnotation b', getAnnotation v')) p b' v'
  UEBundle _ b ->
    let b' = V.map hashCons b
    in UEBundle (hash (hash @Text "Bundle", map getAnnotation $ toList b')) b'


-- toUntypedExpr :: 
--   forall f m ty. (Hashable f, MonadState (BuilderState f) m) => 
--   Expr Wire f ty -> m (SharedUntypedExpr Wire f)
-- toUntypedExpr = \case
--   EVal v -> pure $ intern (UEVal $ case v of
--     ValField f -> f
--     ValBool b -> b)
--   EVar v -> intern <$> case v of
--     VarField i -> pure $ UEVar (UVar i)
--     VarBool i -> do
--       emit $ Mul (Var i) (Var i) i
--       pure $ UEVar (UVar i)
--   EUnOp op e -> fmap intern (UEUnOp (untypeUnOp op) <$> toUntypedExpr e)
--   EBinOp op e1 e2 -> fmap intern . UEBinOp (untypeBinOp op) <$> toUntypedExpr e1 <*> toUntypedExpr e2
--   EIf b t e -> intern <$> (UEIf <$> toUntypedExpr b <*> toUntypedExpr t <*> toUntypedExpr e)
--   EEq l r -> intern  <$> (UEEq <$> toUntypedExpr l <*> (toUntypedExpr r))
--   ESplit i -> intern . UESplit (fromIntegral $ natVal (Proxy @(NBits f))) <$> toUntypedExpr i
--   EJoin i -> intern . UEJoin <$> toUntypedExpr i
--   EAtIndex v i -> fmap intern . UEAtIndex <$> toUntypedExpr v <*> pure (fromIntegral i)
--   EUpdateIndex p b v -> fmap intern . UEUpdateIndex (fromIntegral p) <$> toUntypedExpr b <*> toUntypedExpr v
--   EBundle b -> intern . UEBundle <$> traverse toUntypedExpr (SV.fromSized b)

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
  EAtIndex :: (KnownNat n) => Expr i f (SV.Vector n ty) -> Finite n -> Expr i f ty
  EUpdateIndex :: (KnownNat n) => Finite n -> (Expr i f ty) -> Expr i f (SV.Vector n ty) -> Expr i f (SV.Vector n ty)
  EBundle :: SV.Vector n (Expr i f ty) -> Expr i f (SV.Vector n ty)

deriving instance (Show f) => Show (BinOp f a)

deriving instance (Show f) => Show (UnOp f a)

instance Pretty (BinOp f a) where
  pretty op = case op of
    BAdd -> text "+"
    BSub -> text "-"
    BMul -> text "*"
    BDiv -> text "/"
    BAnd -> text "&&"
    BOr -> text "||"
    BXor -> text "xor"

instance Pretty (UnOp f a) where
  pretty op = case op of
    UNeg -> text "neg"
    UNot -> text "!"

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
          EAtIndex v _ix -> pretty v <+> brackets (pretty $ toInteger _ix)
          EUpdateIndex _p b v -> text ("setIndex " <> Protolude.show (natVal _p)) <+> pretty b <+> pretty v

parensPrec :: Int -> Int -> Doc -> Doc
parensPrec opPrec p = if p > opPrec then parens else identity

-------------------------------------------------------------------------------
-- Evaluator
-------------------------------------------------------------------------------

-- | Truncate a number to the given number of bits and perform a right
-- rotation (assuming small-endianness) within the truncation.
truncRotate ::
  (Bits f) =>
  -- | number of bits to truncate to
  Int ->
  -- | number of bits to rotate by
  Int ->
  f ->
  f
truncRotate nbits nrots x =
  foldr
    ( \_ix rest ->
        if testBit x _ix
          then setBit rest ((_ix + nrots) `mod` nbits)
          else rest
    )
    zeroBits
    [0 .. nbits - 1]

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
  EAtIndex v i -> do
    _v <- evalExpr' v
    pure $ _v `SV.index` i
  EUpdateIndex p b v -> do
    _v <- evalExpr' v
    _b <- evalExpr' b
    pure $ _v & SV.ix p .~ _b

-------------------------------------------------------------------------------
-- Circuit Builder
-------------------------------------------------------------------------------

data BuilderState f = BuilderState
  { bsCircuit :: ArithCircuit f,
    bsNextVar :: Int,
    bsVars :: CircuitVars Text,
    bsSharedMap :: Map Id (UntypedExpr Int Wire f, V.Vector (SignalSource f))
  }

defaultBuilderState :: BuilderState f
defaultBuilderState =
  BuilderState
    { bsCircuit = ArithCircuit [],
      bsNextVar = 1,
      bsVars = mempty,
      bsSharedMap = mempty
    }

-- non recoverable errors that can arise during circuit building
data CircuitBuilderError f
  = ExpectedSingleWire (V.Vector (SignalSource f))
  | MismatchedWireTypes (V.Vector (SignalSource f)) (V.Vector (SignalSource f))

instance (GaloisField f) => Pretty (CircuitBuilderError f) where
  pretty = \case
    ExpectedSingleWire wires -> "Expected a single wire, but got:" <+> pretty (toList wires)
    MismatchedWireTypes l r -> "Mismatched wire types:" <+> pretty (toList l) <+> pretty (toList r)

type ExprM f a = ExceptT (CircuitBuilderError f) (StateT (BuilderState f) IO) a

runExprM :: (GaloisField f) => ExprM f a -> BuilderState f -> IO (a, BuilderState f)
runExprM m s = do
  res <- runStateT (runExceptT m) s
  case res of
    (Left e, _) -> panic $ Protolude.show $ pretty e
    (Right a, s') -> pure $ (a, s')

execCircuitBuilder :: (GaloisField f) => ExprM f a -> IO (ArithCircuit f)
execCircuitBuilder m = reverseCircuit . bsCircuit . snd <$> runExprM m defaultBuilderState
  where
    reverseCircuit = \(ArithCircuit cs) -> ArithCircuit $ reverse cs

evalCircuitBuilder :: (GaloisField f) => ExprM f a -> IO a
evalCircuitBuilder e = fst <$> runCircuitBuilder e

runCircuitBuilder :: (GaloisField f) => ExprM f a -> IO (a, BuilderState f)
runCircuitBuilder m = do
  (a, s) <- runExprM m defaultBuilderState
  pure
    ( a,
      s
        { bsCircuit = reverseCircuit $ bsCircuit s
        }
    )
  where
    reverseCircuit = \(ArithCircuit cs) -> ArithCircuit $ reverse cs

--------------------------------------------------------------------------------

fresh :: (MonadState (BuilderState f) m) => m Int
fresh = do
  v <- gets bsNextVar
  modify $ \s ->
    s
      { bsVars = (bsVars s) {cvVars = Set.insert v (cvVars $ bsVars s)},
        bsNextVar = v + 1
      }
  pure v

-- | Fresh intermediate variables
imm :: (MonadState (BuilderState f) m) => m Wire
imm = IntermediateWire <$> fresh

-- | Fresh input variables
freshPublicInput :: (MonadState (BuilderState f) m) => Text -> m Wire
freshPublicInput label = do
  v <- InputWire label Public <$> fresh
  modify $ \s ->
    s
      { bsVars =
          (bsVars s)
            { cvPublicInputs = Set.insert (wireName v) (cvPublicInputs $ bsVars s),
              cvInputsLabels = Map.insert label (wireName v) (cvInputsLabels $ bsVars s)
            }
      }
  pure v

freshPrivateInput :: (MonadState (BuilderState f) m) => Text -> m Wire
freshPrivateInput label = do
  v <- InputWire label Private <$> fresh
  modify $ \s ->
    s
      { bsVars =
          (bsVars s)
            { cvPrivateInputs = Set.insert (wireName v) (cvPrivateInputs $ bsVars s),
              cvInputsLabels = Map.insert label (wireName v) (cvInputsLabels $ bsVars s)
            }
      }
  pure v

-- | Fresh output variables
freshOutput :: (MonadState (BuilderState f) m) => m Wire
freshOutput = do
  v <- OutputWire <$> fresh
  modify $ \s ->
    s
      { bsVars =
          (bsVars s)
            { cvOutputs = Set.insert (wireName v) (cvOutputs $ bsVars s)
            }
      }
  pure v

-- This allows for an optimization to avoid creating a new variable/constraint in the event that
-- the output of an expression is already a wire
data SignalSource f
  = WireSource Wire
  | AffineSource (AffineCircuit f Wire)
    deriving (Show)

instance (Show f) => Pretty (SignalSource f) where
  pretty = \case
    WireSource w -> pretty w
    AffineSource c -> pretty c

-- | Multiply two wires or affine circuits to an intermediate variable
mulToImm :: (MonadState (BuilderState f) m) => SignalSource f -> SignalSource f -> m Wire
mulToImm l r = do
  o <- imm
  emit $ Mul (addVar l) (addVar r) o
  pure o

-- | Add a Mul and its output to the ArithCircuit
emit :: (MonadState (BuilderState f) m) => Gate f Wire -> m ()
emit c = modify $ \s@(BuilderState {bsCircuit = ArithCircuit cs}) ->
  s {bsCircuit = ArithCircuit (c : cs)}

-- | Rotate a list to the right
rotateList :: Int -> [a] -> [a]
rotateList steps x = take (length x) $ drop steps $ cycle x

-- | Turn a wire into an affine circuit, or leave it be
addVar :: SignalSource f -> AffineCircuit f Wire
addVar s = case s of
  WireSource w -> Var w
  AffineSource c -> c

-- | Turn an affine circuit into a wire, or leave it be
addWire :: (MonadState (BuilderState f) m, Num f) => SignalSource f -> m Wire
addWire x = case x of
  WireSource w -> pure w
  AffineSource c -> do
    mulOut <- imm
    emit $ Mul (ConstGate 1) c mulOut
    pure mulOut

compileWithWire ::
  (Hashable f, GaloisField f) =>
  (MonadIO m) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  m (Var Wire f ty) ->
  Expr Wire f ty ->
  m Wire
compileWithWire freshWire e = do
  V.head
    <$> compileWithWires (V.singleton $ fmap coerceGroundType freshWire) e

compileWithWires ::
  (Hashable f, GaloisField f) =>
  (MonadIO m) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  V.Vector (m (Var Wire f f)) ->
  Expr Wire f ty ->
  m (V.Vector Wire)
compileWithWires ws expr = do
  let e = hashCons $ unType expr
  compileOut <- memoizedCompile $ e 
  for (V.zip compileOut ws) $ \(o, freshWire) -> do
    case o of
      WireSource wire -> do
        wire' <- rawWire <$> freshWire
        emit $ Mul (ConstGate 1) (Var wire') wire
        pure wire
      AffineSource circ -> do
        wire <- rawWire <$> freshWire
        emit $ Mul (ConstGate 1) circ wire
        pure wire

assertSingleSource ::
  (MonadError (CircuitBuilderError f) m) =>
  V.Vector (SignalSource f) ->
  m (SignalSource f)
assertSingleSource xs = case xs V.!? 0 of
  Just x -> pure x
  _ -> throwError $ ExpectedSingleWire xs

assertSameSourceSize ::
  (MonadError (CircuitBuilderError f) m) =>
  V.Vector (SignalSource f) ->
  V.Vector (SignalSource f) ->
  m ()
assertSameSourceSize l r =
  unless (V.length l == V.length r) $
    throwError $
      MismatchedWireTypes l r

_compile ::
  forall f m.
  (Hashable f, GaloisField f) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  UntypedExpr Int Wire f ->
  m (V.Vector (SignalSource f))
_compile expr = case expr of
  UEVal i v ->
    case v of
      f -> do 
        let res = V.singleton $ AffineSource $ ConstGate f
        modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
        pure res
  UEVar i (UVar var) -> do
    let res = V.singleton $ WireSource var
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  UEUnOp i op e1 -> do
    e1Outs <- memoizedCompile e1
    res <- for e1Outs $ \e1Out ->
          case op of
            UUNeg -> pure . AffineSource $ ScalarMul (-1) (addVar e1Out)
            UUNot -> pure . AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (addVar e1Out))
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  UEBinOp i op e1 e2 -> do
    e1Outs <- memoizedCompile e1
    e2Outs <- memoizedCompile e2
    assertSameSourceSize e1Outs e2Outs
    res <- for (V.zip (addVar <$> e1Outs) (addVar <$> e2Outs)) $ \(e1Out, e2Out) ->
      case op of
        UAdd -> pure . AffineSource $ Add e1Out e2Out
        UMul -> do
          tmp1 <- mulToImm (AffineSource e1Out) (AffineSource e2Out)
          pure . WireSource $ tmp1
        UDiv -> do
          _recip <- imm
          _one <- addWire $ AffineSource $ ConstGate 1
          emit $ Mul e2Out (Var _recip) _one
          out <- imm
          emit $ Mul e1Out (Var _recip) out
          pure $ WireSource out
        -- SUB(x, y) = x + (-y)
        USub -> pure . AffineSource $ Add e1Out (ScalarMul (-1) e2Out)
        UAnd -> do
          tmp1 <- mulToImm (AffineSource e1Out) (AffineSource e2Out)
          pure . WireSource $ tmp1
        UOr -> do
          -- OR(input1, input2) = (input1 + input2) - (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure . AffineSource $ Add (Add e1Out e2Out) (ScalarMul (-1) (Var tmp1))
        UXor -> do
          -- XOR(input1, input2) = (input1 + input2) - 2 * (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure . AffineSource $ Add (Add e1Out e2Out) (ScalarMul (-2) (Var tmp1))
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  -- IF(cond, true, false) = (cond*true) + ((!cond) * false)
  UEIf i cond true false -> do
    res <- V.singleton <$> do
      condOut <- addVar <$> (memoizedCompile cond >>= assertSingleSource)
      trueOuts <- memoizedCompile true
      falseOuts <- memoizedCompile false
      assertSameSourceSize trueOuts falseOuts
      tmp1 <- imm
      for_ (addVar <$> trueOuts) $ \trueOut ->
        emit $ Mul condOut trueOut tmp1
      tmp2 <- imm
      for_ (addVar <$> falseOuts) $ \falseOut ->
        emit $ Mul (Add (ConstGate 1) (ScalarMul (-1) condOut)) falseOut tmp2
      pure . AffineSource $ Add (Var tmp1) (Var tmp2)
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  -- EQ(lhs, rhs) = (lhs - rhs == 1) only allowed for field comparison
  UEEq i lhs rhs -> do
    res <- V.singleton <$> do
      -- assertSingle is justified as the lhs and rhs must be of type f
      let e = UEBinOp (hash (USub, getAnnotation lhs, getAnnotation rhs)) USub lhs rhs
      r <- memoizedCompile e >>= assertSingleSource
      modify $ \s -> s {bsSharedMap = Map.insert (getAnnotation e) (e, V.singleton r) (bsSharedMap s)}
      eqInWire <- addWire r
      eqFreeWire <- imm
      eqOutWire <- imm
      emit $ Equal eqInWire eqFreeWire eqOutWire
      -- eqOutWire == 0 if lhs == rhs, so we need to return 1 -
      -- neqOutWire instead.
      pure . AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (Var eqOutWire))
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  UESplit _i n input -> do
    res <- do
      -- assertSingle is justified as the input must be of type f
      i <- memoizedCompile input >>= assertSingleSource >>= addWire
      outputs <- V.generateM n (const $ mkBoolVar =<< imm)
      emit $ Split i (V.toList outputs)
      fold <$> (for outputs $ \o -> 
        let v = UVar o
            e = UEVar (hash v) v
        in memoizedCompile e)
    modify $ \s -> s {bsSharedMap = Map.insert _i (expr, res) (bsSharedMap s)}
    pure res
      where
        mkBoolVar w = do
          emit $ Mul (Var w) (Var w) w
          pure w
  UEBundle i as -> do
    res <- do
      as' <- traverse memoizedCompile as
      pure $ fold as'
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  UEJoin i bits -> do
    res <- V.singleton <$> do
      bs <- toList <$> memoizedCompile bits
      ws <- traverse addWire bs
      pure . AffineSource $ unsplit ws
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  UEAtIndex i v _ix -> do
    res <- V.singleton <$> do
      v' <- memoizedCompile v
      pure $ v' V.! (fromIntegral _ix)
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
  UEUpdateIndex i p b v -> do
    res <- do
      v' <- memoizedCompile v
      b' <- memoizedCompile b >>= assertSingleSource
      let p' = fromIntegral p
      pure $ V.imap (\_ix w -> if _ix == p' then b' else w) v'
    modify $ \s -> s {bsSharedMap = Map.insert i (expr, res) (bsSharedMap s)}
    pure res
    

memoizedCompile ::
  forall f m.
  (Hashable f, GaloisField f) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  UntypedExpr Int Wire f ->
  m (V.Vector (SignalSource f))
memoizedCompile expr = do 
  m <- gets bsSharedMap
  case Map.lookup (getAnnotation expr) m of
    Just (e, ws) -> pure ws
      --if (expr /= e) 
      --  then do 
      --    traceM $ "COLLISION"
      --    traceM $ show expr
      --    traceM "with"
      --    traceM $ show e
      --    panic "Cache is fucked"
      --  else pure ws
    Nothing -> _compile expr

exprToArithCircuit ::
  (Hashable  f, GaloisField f) =>
  -- \| expression to compile
  Expr Wire f ty ->
  -- | Wire to assign the output of the expression to
  Wire ->
  ExprM f ()
exprToArithCircuit expr output = do
  let e  = hashCons $ unType expr
  compileOut <- memoizedCompile e >>= assertSingleSource
  emit $ Mul (ConstGate 1) (addVar compileOut) output

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


{-

  SUEVar 630 (UVar (InputWire "cell_(0,1)" Public 2))


  SUEEq 630 
    (SUEVal 452 (P (1 `modulo` 21888242871839275222246405745257275088548364400416034343698204186575808495617))) 
    (SUEIf 514 
      (SUEEq 656 
        (SUEVar 629 (UVar (InputWire "cell_(0,0)" Public 1))) 
        (SUEVal 453 (P (0 `modulo` 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
      ) 
      (SUEVar 550 (UVar (InputWire "private_cell_(0,0)" Private 82))) 
      (SUEVar 629 (UVar (InputWire "cell_(0,0)" Public 1))))
-}