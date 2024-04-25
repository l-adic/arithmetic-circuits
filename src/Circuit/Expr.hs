{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Circuit.Expr
  ( UnOp (..),
    BinOp (..),
    Val (..),
    Var (..),
    Expr (..),
    ExprM,
    BuilderState (..),
    type NBits,
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
  )
where

import Circuit.Affine
import Circuit.Arithmetic
import Data.Field.Galois (GaloisField, PrimeField (fromP))
import Data.Finite (Finite)
import Data.Map qualified as Map
import Data.Semiring (Ring (..), Semiring (..))
import Data.Set qualified as Set
import Data.Vector.Sized (Vector)
import Data.Vector.Sized qualified as V
import Protolude hiding (Semiring)
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Lens.Micro ((.~))


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

-- | Expression data type of (arithmetic) expressions over a field @f@
-- with variable names/indices coming from @i@.
data Expr i f t ty where
  EVal :: Val f ty -> Expr i f Identity ty
  EVar :: Var i f ty -> Expr i f Identity ty
  EUnOp :: UnOp f ty -> Expr i f Identity ty -> Expr i f Identity ty
  EBinOp :: BinOp f ty -> Expr i f Identity ty -> Expr i f Identity ty -> Expr i f Identity ty
  EIf :: Expr i f Identity Bool -> Expr i f Identity ty -> Expr i f Identity ty -> Expr i f Identity ty
  EEq :: Expr i f Identity f -> Expr i f Identity f -> Expr i f Identity Bool
  ESplit :: (KnownNat (NBits f)) => Expr i f Identity f -> Expr i f (Vector (NBits f)) Bool
  EJoin :: (Num f, KnownNat n) => Expr i f (Vector n) Bool -> Expr i f Identity f
  EAtIndex :: (KnownNat n) => Expr i f (Vector n) ty -> Finite n -> Expr i f Identity ty
  EUpdateIndex :: (KnownNat n) => Finite n -> (Expr i f Identity ty) -> Expr i f (Vector n) ty ->  Expr i f  (Vector n) ty

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

instance (Pretty f, Pretty i) => Pretty (Expr i f t ty) where
  pretty = prettyPrec 0
    where
      prettyPrec :: Int -> Expr i f t ty -> Doc
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
          EJoin i -> text "join" <+> pretty i
          EAtIndex v ix -> pretty v <+> brackets (pretty $ toInteger ix)
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
    ( \ix rest ->
        if testBit x ix
          then setBit rest ((ix + nrots) `mod` nbits)
          else rest
    )
    zeroBits
    [0 .. nbits - 1]

evalExpr :: (PrimeField f, Ord i, Show i) => Map i f -> Expr i f t ty -> t ty
evalExpr inputs e = evalState (evalExpr' e) inputs

-- | Evaluate arithmetic expressions directly, given an environment
evalExpr' ::
  forall f i t ty.
  (PrimeField f, Ord i, Show i) =>
  -- | variable lookup
  -- | expression to evaluate
  Expr i f t ty ->
  -- | input values
  -- | resulting value
  State (Map i f) (t ty)
evalExpr' expr = case expr of
  EVal v -> pure $ Identity $ case v of
    ValBool b -> b == 1
    ValField f -> f
  EVar var -> do
    m <- get
    pure $ Identity $ case var of
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
    fmap not <$> evalExpr' e1
  EBinOp op e1 e2 -> do
    e1' <- runIdentity <$> evalExpr' e1
    e2' <- runIdentity <$> evalExpr' e2
    pure $ Identity $ apply e1' e2'
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
    cond <- runIdentity <$> evalExpr' b
    if cond
      then evalExpr' true
      else evalExpr' false
  EEq lhs rhs -> do
    lhs' <- runIdentity <$> evalExpr' lhs
    rhs' <- runIdentity <$> evalExpr' rhs
    pure $ Identity $ lhs' == rhs'
  ESplit i -> do
    x <- runIdentity <$> evalExpr' i
    pure $ V.generate $ \ix -> testBit (fromP x) (fromIntegral ix)
  EJoin i -> do
    bits <- evalExpr' i
    pure $
      Identity $
        V.ifoldl (\acc ix b -> acc + if b then fromInteger (2 ^ fromIntegral @_ @Integer ix) else 0) 0 bits
  EAtIndex v i -> do
    _v <- evalExpr' v
    pure $ Identity $ _v `V.index` i
  EUpdateIndex p b v -> do
    _v <- evalExpr' v
    _b <- runIdentity <$> evalExpr' b
    pure $ _v & V.ix p .~ _b


--   pure $ Vec.fromList $ map (testBit i) [0 .. Nat.toInt (Vec.length i) - 1]

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

type ExprM f a = State (BuilderState f) a

execCircuitBuilder :: ExprM f a -> ArithCircuit f
execCircuitBuilder m = reverseCircuit $ bsCircuit $ execState m defaultBuilderState
  where
    reverseCircuit = \(ArithCircuit cs) -> ArithCircuit $ reverse cs

evalCircuitBuilder :: ExprM f a -> a
evalCircuitBuilder = fst . runCircuitBuilder

runCircuitBuilder :: ExprM f a -> (a, BuilderState f)
runCircuitBuilder m =
  let (a, s) = runState m defaultBuilderState
   in ( a,
        s
          { bsCircuit = reverseCircuit $ bsCircuit s
          }
      )
  where
    reverseCircuit = \(ArithCircuit cs) -> ArithCircuit $ reverse cs

fresh :: ExprM f Int
fresh = do
  v <- gets bsNextVar
  modify $ \s ->
    s
      { bsVars = (bsVars s) {cvVars = Set.insert v (cvVars $ bsVars s)},
        bsNextVar = v + 1
      }
  pure v

-- | Fresh intermediate variables
imm :: ExprM f Wire
imm = IntermediateWire <$> fresh

-- | Fresh input variables
freshPublicInput :: Text -> ExprM f Wire
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

freshPrivateInput :: Text -> ExprM f Wire
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
freshOutput :: ExprM f Wire
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

-- | Multiply two wires or affine circuits to an intermediate variable
mulToImm :: Either Wire (AffineCircuit f Wire) -> Either Wire (AffineCircuit f Wire) -> ExprM f Wire
mulToImm l r = do
  o <- imm
  emit $ Mul (addVar l) (addVar r) o
  pure o

-- | Add a Mul and its output to the ArithCircuit
emit :: Gate f Wire -> ExprM f ()
emit c = modify $ \s@(BuilderState {bsCircuit = ArithCircuit cs}) ->
  s {bsCircuit = ArithCircuit (c : cs)}

-- | Rotate a list to the right
rotateList :: Int -> [a] -> [a]
rotateList steps x = take (length x) $ drop steps $ cycle x

-- | Turn a wire into an affine circuit, or leave it be
addVar :: Either Wire (AffineCircuit f Wire) -> AffineCircuit f Wire
addVar (Left w) = Var w
addVar (Right c) = c

-- | Turn an affine circuit into a wire, or leave it be
addWire :: (Num f) => Either Wire (AffineCircuit f Wire) -> ExprM f Wire
addWire (Left w) = pure w
addWire (Right c) = do
  mulOut <- imm
  emit $ Mul (ConstGate 1) c mulOut
  pure mulOut

compile ::
  forall f t ty.
  (Num f) =>
  Expr Wire f t ty ->
  ExprM f (t (Either Wire (AffineCircuit f Wire)))
compile expr = case expr of
  EVal v -> case v of
    ValField f -> pure . Identity $ Right $ ConstGate f
    ValBool b -> pure . Identity $ Right $ ConstGate b
  EVar var -> case var of
    VarField i -> pure . Identity $ Left i
    VarBool i -> do
      squared <- mulToImm (Left i) (Left i)
      emit $ Mul (Var squared) (ConstGate 1) i
      pure $ Identity $ Left i
  EUnOp op e1 -> do
    e1Out <- runIdentity <$> compile e1
    case op of
      UNeg -> pure . Identity . Right $ ScalarMul (-1) (addVar e1Out)
      UNot -> pure . Identity . Right $ Add (ConstGate 1) (ScalarMul (-1) (addVar e1Out))
  EBinOp op e1 e2 -> do
    e1Out <- addVar . runIdentity <$> compile e1
    e2Out <- addVar . runIdentity <$> compile e2
    case op of
      BAdd -> pure . Identity . Right $ Add e1Out e2Out
      BMul -> do
        tmp1 <- mulToImm (Right e1Out) (Right e2Out)
        pure . Identity . Left $ tmp1
      BDiv -> do
        _recip <- imm
        _one <- addWire $ Right $ ConstGate 1
        emit $ Mul e2Out (Var _recip) _one
        out <- imm
        emit $ Mul e1Out (Var _recip) out
        pure $ Identity $ Left out
      -- SUB(x, y) = x + (-y)
      BSub -> pure . Identity . Right $ Add e1Out (ScalarMul (-1) e2Out)
      BAnd -> do
        tmp1 <- mulToImm (Right e1Out) (Right e2Out)
        pure . Identity . Left $ tmp1
      BOr -> do
        -- OR(input1, input2) = (input1 + input2) - (input1 * input2)
        tmp1 <- imm
        emit $ Mul e1Out e2Out tmp1
        pure . Identity . Right $ Add (Add e1Out e2Out) (ScalarMul (-1) (Var tmp1))
      BXor -> do
        -- XOR(input1, input2) = (input1 + input2) - 2 * (input1 * input2)
        tmp1 <- imm
        emit $ Mul e1Out e2Out tmp1
        pure . Identity . Right $ Add (Add e1Out e2Out) (ScalarMul (-2) (Var tmp1))
  -- IF(cond, true, false) = (cond*true) + ((!cond) * false)
  EIf cond true false -> do
    condOut <- addVar . runIdentity <$> compile cond
    trueOut <- addVar . runIdentity <$> compile true
    falseOut <- addVar . runIdentity <$> compile false
    tmp1 <- imm
    tmp2 <- imm
    emit $ Mul condOut trueOut tmp1
    emit $ Mul (Add (ConstGate 1) (ScalarMul (-1) condOut)) falseOut tmp2
    pure . Identity . Right $ Add (Var tmp1) (Var tmp2)
  -- EQ(lhs, rhs) = (lhs - rhs == 1)
  EEq lhs rhs -> do
    lhsSubRhs <- runIdentity <$> compile (EBinOp BSub lhs rhs)
    eqInWire <- addWire lhsSubRhs
    eqFreeWire <- imm
    eqOutWire <- imm
    emit $ Equal eqInWire eqFreeWire eqOutWire
    -- eqOutWire == 0 if lhs == rhs, so we need to return 1 -
    -- neqOutWire instead.
    pure . Identity $ Right $ Add (ConstGate 1) (ScalarMul (-1) (Var eqOutWire))
  ESplit input -> do
    i <- compile input >>= addWire . runIdentity
    outputs <- traverse (\_ -> mkBoolVar =<< imm) $ universe @(NBits f)
    emit $ Split i (V.toList outputs)
    traverse (fmap runIdentity . compile . EVar . VarBool) outputs
    where
      mkBoolVar w = do
        squared <- mulToImm (Left w) (Left w)
        emit $ Mul (Var squared) (ConstGate 1) w
        pure w
  EJoin bits -> do
    bs <- toList <$> compile bits
    ws <- traverse addWire bs
    pure . Identity . Right $ unsplit ws
  EAtIndex v ix -> do
    v' <- compile v
    pure . Identity $ v' `V.index` ix
  EUpdateIndex p b v -> do
    v' <- compile v
    b' <- runIdentity <$> compile b
    pure $ v' & V.ix p .~ b'

exprToArithCircuit ::
  (Num f, Foldable t) =>
  -- \| expression to compile
  Expr Wire f t ty ->
  -- | Wire to assign the output of the expression to
  t Wire ->
  ExprM f ()
exprToArithCircuit expr outputs = do
  exprOuts <- toList <$> compile expr
  for_ (zip (toList outputs) exprOuts) $ \(output, exprOut) ->
    emit $ Mul (ConstGate 1) (addVar exprOut) output

instance (GaloisField f) => Semiring (Expr Wire f Identity f) where
  plus = EBinOp BAdd
  zero = EVal $ ValField 0
  times = EBinOp BMul
  one = EVal $ ValField 1

instance (GaloisField f) => Ring (Expr Wire f Identity f) where
  negate = EUnOp UNeg

instance (GaloisField f) => Num (Expr Wire f Identity f) where
  (+) = plus
  (*) = times
  (-) = EBinOp BSub
  negate = EUnOp UNeg
  abs = identity
  signum = const 1
  fromInteger = EVal . ValField . fromInteger

universe :: (KnownNat n) => Vector n (Finite n)
universe = V.enumFromN 0
