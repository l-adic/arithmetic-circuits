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
    Ground,
    compile,
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
    exprToArithCircuit,
    compileWithWire,
  )
where

import Circuit.Affine
import Circuit.Arithmetic
import Data.Field.Galois (GaloisField, PrimeField (fromP))
import Data.Finite (Finite)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Semigroup qualified as NE
import Data.Semiring (Ring (..), Semiring (..))
import Data.Set qualified as Set
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as V
import Lens.Micro (ix, (.~))
import Protolude hiding (Semiring)
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Prelude (foldl1)

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

type family NBits a :: Nat

-- | This constring prevents us from building up nested vectors inside the expression type
class (GaloisField f) => Ground f ty

instance (GaloisField f) => Ground f f

instance (GaloisField f) => Ground f Bool

-- | Expression data type of (arithmetic) expressions over a field @f@
-- with variable names/indices coming from @i@.
data Expr i f ty where
  EVal :: Val f ty -> Expr i f ty
  EVar :: Var i f ty -> Expr i f ty
  EUnOp :: UnOp f ty -> Expr i f ty -> Expr i f ty
  EBinOp :: BinOp f ty -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EIf :: Expr i f Bool -> Expr i f ty -> Expr i f ty -> Expr i f ty
  EEq :: Expr i f f -> Expr i f f -> Expr i f Bool
  ESplit :: (KnownNat (NBits f)) => Expr i f f -> Expr i f (Vector (NBits f) Bool)
  EJoin :: (KnownNat n) => Expr i f (Vector n Bool) -> Expr i f f
  EAtIndex :: (KnownNat n, Ground f ty) => Expr i f (Vector n ty) -> Finite n -> Expr i f ty
  EUpdateIndex :: (KnownNat n, Ground f ty) => Finite n -> (Expr i f ty) -> Expr i f (Vector n ty) -> Expr i f (Vector n ty)
  EBundle :: (Ground f ty) => Vector n (Expr i f ty) -> Expr i f (Vector n ty)

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
          ESplit i -> text "split" <+> pretty i
          EBundle b -> text "bundle" <+> pretty (V.toList b)
          EJoin i -> text "join" <+> pretty i
          EAtIndex v _ix -> pretty v <+> brackets (pretty $ toInteger _ix)
          EUpdateIndex _p b v -> text ("setIndex " <> show (natVal _p)) <+> pretty b <+> pretty v

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
          Nothing -> panic $ "TODO: incorrect var lookup: " <> show i
      VarBool i ->
        case Map.lookup i m of
          Just v -> v == 1
          Nothing -> panic $ "TODO: incorrect var lookup: " <> show i
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
    pure $ V.generate $ \_ix -> testBit (fromP x) (fromIntegral _ix)
  EBundle as -> traverse evalExpr' as
  EJoin i -> do
    bits <- evalExpr' i
    pure $
      V.ifoldl (\acc _ix b -> acc + if b then fromInteger (2 ^ fromIntegral @_ @Integer _ix) else 0) 0 bits
  EAtIndex v i -> do
    _v <- evalExpr' v
    pure $ _v `V.index` i
  EUpdateIndex p b v -> do
    _v <- evalExpr' v
    _b <- evalExpr' b
    pure $ _v & V.ix p .~ _b

-------------------------------------------------------------------------------
-- Circuit Builder
-------------------------------------------------------------------------------

data BuilderState f = BuilderState
  { bsCircuit :: ArithCircuit f,
    bsNextVar :: Int,
    bsVars :: CircuitVars Text
  }

defaultBuilderState :: BuilderState f
defaultBuilderState =
  BuilderState
    { bsCircuit = ArithCircuit [],
      bsNextVar = 1,
      bsVars = mempty
    }

-- non recoverable errors that can arise during circuit building
data CircuitBuilderError f
  = ExpectedSingleWire (NonEmpty (SignalSource f))
  | MismatchedWireTypes (NonEmpty (SignalSource f)) (NonEmpty (SignalSource f))

instance (GaloisField f) => Pretty (CircuitBuilderError f) where
  pretty = \case
    ExpectedSingleWire wires -> "Expected a single wire, but got:" <+> pretty (toList wires)
    MismatchedWireTypes l r -> "Mismatched wire types:" <+> pretty (toList l) <+> pretty (toList r)

type ExprM f a = ExceptT (CircuitBuilderError f) (State (BuilderState f)) a

runExprM :: (GaloisField f) => ExprM f a -> BuilderState f -> (a, BuilderState f)
runExprM m s = case runState (runExceptT m) s of
  (Left e, _) -> panic $ show $ pretty e
  (Right a, s') -> (a, s')

execCircuitBuilder :: (GaloisField f) => ExprM f a -> ArithCircuit f
execCircuitBuilder m = reverseCircuit $ bsCircuit $ snd $ runExprM m defaultBuilderState
  where
    reverseCircuit = \(ArithCircuit cs) -> ArithCircuit $ reverse cs

evalCircuitBuilder :: (GaloisField f) => ExprM f a -> a
evalCircuitBuilder = fst . runCircuitBuilder

runCircuitBuilder :: (GaloisField f) => ExprM f a -> (a, BuilderState f)
runCircuitBuilder m =
  let (a, s) = runExprM m defaultBuilderState
   in ( a,
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
  (Num f, MonadState (BuilderState f) m, MonadError (CircuitBuilderError f) m) =>
  m (Var Wire f ty) ->
  Expr Wire f ty ->
  m Wire
compileWithWire freshWire expr = do
  compileOut <- compile expr >>= assertSingleSource
  case compileOut of
    WireSource wire -> do
      wire' <- rawWire <$> freshWire
      emit $ Mul (ConstGate 1) (Var wire') wire
      pure wire
    AffineSource circ -> do
      wire <- rawWire <$> freshWire
      emit $ Mul (ConstGate 1) circ wire
      pure wire

assertSingleSource :: (MonadError (CircuitBuilderError f) m) => NonEmpty (SignalSource f) -> m (SignalSource f)
assertSingleSource xs = case xs of
  x NE.:| [] -> pure x
  _ -> throwError $ ExpectedSingleWire xs

assertSameSourceSize :: (MonadError (CircuitBuilderError f) m) => NonEmpty (SignalSource f) -> NonEmpty (SignalSource f) -> m ()
assertSameSourceSize l r =
  unless (NE.length l == NE.length r) $
    throwError $
      MismatchedWireTypes l r

compile ::
  forall f m ty.
  (Num f) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  Expr Wire f ty ->
  m (NonEmpty (SignalSource f))
compile expr = case expr of
  EVal v ->
    NE.singleton <$> case v of
      ValField f -> pure . AffineSource $ ConstGate f
      ValBool b -> pure . AffineSource $ ConstGate b
  EVar var ->
    NE.singleton <$> case var of
      VarField i -> pure . WireSource $ i
      VarBool i -> do
        squared <- mulToImm (WireSource i) (WireSource i)
        emit $ Mul (Var squared) (ConstGate 1) i
        pure . WireSource $ i
  EUnOp op e1 -> do
    e1Outs <- compile e1
    for e1Outs $ \e1Out ->
      case op of
        UNeg -> pure . AffineSource $ ScalarMul (-1) (addVar e1Out)
        UNot -> pure . AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (addVar e1Out))
  EBinOp op e1 e2 -> do
    e1Outs <- compile e1
    e2Outs <- compile e2
    assertSameSourceSize e1Outs e2Outs
    for (NE.zip (addVar <$> e1Outs) (addVar <$> e2Outs)) $ \(e1Out, e2Out) ->
      case op of
        BAdd -> pure . AffineSource $ Add e1Out e2Out
        BMul -> do
          tmp1 <- mulToImm (AffineSource e1Out) (AffineSource e2Out)
          pure . WireSource $ tmp1
        BDiv -> do
          _recip <- imm
          _one <- addWire $ AffineSource $ ConstGate 1
          emit $ Mul e2Out (Var _recip) _one
          out <- imm
          emit $ Mul e1Out (Var _recip) out
          pure $ WireSource out
        -- SUB(x, y) = x + (-y)
        BSub -> pure . AffineSource $ Add e1Out (ScalarMul (-1) e2Out)
        BAnd -> do
          tmp1 <- mulToImm (AffineSource e1Out) (AffineSource e2Out)
          pure . WireSource $ tmp1
        BOr -> do
          -- OR(input1, input2) = (input1 + input2) - (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure . AffineSource $ Add (Add e1Out e2Out) (ScalarMul (-1) (Var tmp1))
        BXor -> do
          -- XOR(input1, input2) = (input1 + input2) - 2 * (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure . AffineSource $ Add (Add e1Out e2Out) (ScalarMul (-2) (Var tmp1))
  -- IF(cond, true, false) = (cond*true) + ((!cond) * false)
  EIf cond true false -> do
    condOut <- addVar <$> (compile cond >>= assertSingleSource)
    trueOuts <- compile true
    falseOuts <- compile false
    assertSameSourceSize trueOuts falseOuts
    tmp1 <- imm
    for_ (addVar <$>  trueOuts) $ \trueOut -> 
      emit $ Mul condOut trueOut tmp1
    tmp2 <- imm
    for_ (addVar <$> falseOuts) $ \falseOut ->
      emit $ Mul (Add (ConstGate 1) (ScalarMul (-1) condOut)) falseOut tmp2
    pure . NE.singleton . AffineSource $ Add (Var tmp1) (Var tmp2)
  -- EQ(lhs, rhs) = (lhs - rhs == 1) only allowed for field comparison
  EEq lhs rhs ->
    NE.singleton <$> do
      -- assertSingle is justified as the lhs and rhs must be of type f
      eqInWire <- compile (EBinOp BSub lhs rhs) >>= assertSingleSource >>= addWire
      eqFreeWire <- imm
      eqOutWire <- imm
      emit $ Equal eqInWire eqFreeWire eqOutWire
      -- eqOutWire == 0 if lhs == rhs, so we need to return 1 -
      -- neqOutWire instead.
      pure . AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (Var eqOutWire))
  ESplit input -> do
    -- assertSingle is justified as the input must be of type f
    i <- compile input >>= assertSingleSource >>= addWire
    outputs <- traverse (const $ mkBoolVar =<< imm) $ universe @(NBits f)
    emit $ Split i (V.toList outputs)
    NE.sconcat <$> traverse (compile . EVar . VarBool) (NE.fromList . V.toList $ outputs)
    where
      mkBoolVar w = do
        squared <- mulToImm (WireSource w) (WireSource w)
        emit $ Mul (Var squared) (ConstGate 1) w
        pure w
  EBundle as -> do
    as' <- traverse compile as
    pure $ Prelude.foldl1 (<>) (toList as')
  EJoin bits ->
    NE.singleton <$> do
      bs <- toList <$> compile bits
      ws <- traverse addWire bs
      pure . AffineSource $ unsplit ws
  EAtIndex v _ix ->
    NE.singleton <$> do
      v' <- compile v
      pure $ v' NE.!! (fromIntegral _ix)
  EUpdateIndex p b v -> do
    v' <- compile v
    b' <- compile b >>= assertSingleSource
    pure $ v' & ix (fromIntegral p) .~ b'

exprToArithCircuit ::
  (Num f) =>
  -- \| expression to compile
  Expr Wire f ty ->
  -- | Wire to assign the output of the expression to
  Wire ->
  ExprM f ()
exprToArithCircuit expr output = do
  exprOut <- compile expr >>= assertSingleSource
  emit $ Mul (ConstGate 1) (addVar exprOut) output

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

universe :: (KnownNat n) => Vector n (Finite n)
universe = V.enumFromN 0
