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
    assertSingle
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
import Data.List.NonEmpty qualified as NE
import Prelude (foldl1)
import Lens.Micro ( (.~), ix )


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
data Expr i f ty where
  EVal :: Val f ty -> Expr i f ty
  EVar :: Var i f ty -> Expr i f  ty
  EUnOp :: UnOp f ty -> Expr i f ty -> Expr i f  ty
  EBinOp :: BinOp f ty -> Expr i f ty -> Expr i f  ty -> Expr i f  ty
  EIf :: Expr i f  Bool -> Expr i f ty -> Expr i f  ty -> Expr i f  ty
  EEq :: Expr i f f -> Expr i f  f -> Expr i f Bool
  ESplit :: (KnownNat (NBits f)) => Expr i f f -> Expr i f (Vector (NBits f) Bool)
  EBundle :: Vector n (Expr i f f) -> Expr i f (Vector n f)
  EJoin :: (KnownNat n) => Expr i f (Vector n Bool) -> Expr i f f
  EAtIndex :: (KnownNat n) => Expr i f (Vector n ty) -> Finite n -> Expr i f ty
  EUpdateIndex :: (KnownNat n) => Finite n -> (Expr i f f) -> Expr i f (Vector n f) ->  Expr i f  (Vector n f)

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
          EBundle _ -> panic ""
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
    pure $  case var of
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
    e1' <-  evalExpr' e1
    e2' <-  evalExpr' e2
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

--------------------------------------------------------------------------------

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
addVar = either Var identity

-- | Turn an affine circuit into a wire, or leave it be
addWire :: (Num f) => Either Wire (AffineCircuit f Wire) -> ExprM f Wire
addWire x = case x of
  Left w -> pure w
  Right c -> do
    mulOut <- imm
    emit $ Mul (ConstGate 1) c mulOut
    pure mulOut

assertSingle :: NonEmpty a -> a 
assertSingle xs = case xs of
  x NE.:| [] -> x
  _ -> panic "Expected single wire"

compile ::
  forall f ty.
  (Num f) =>
  Expr Wire f ty ->
  ExprM f (NonEmpty (Either Wire (AffineCircuit f Wire)))
compile expr = case expr of
  EVal v -> NE.singleton <$> case v of
    ValField f -> pure . Right $ ConstGate f
    ValBool b -> pure . Right $ ConstGate b
  EVar var ->  NE.singleton <$> case var of
    VarField i -> pure . Left $ i
    VarBool i ->do
      squared <- mulToImm  (Left i) (Left i)
      emit $ Mul (Var squared) (ConstGate 1) i
      pure . Left $ i
  EUnOp op e1 -> do
    e1Outs <- compile e1
    for e1Outs $ \e1Out ->
      case op of
          UNeg -> pure . Right $ ScalarMul (-1) (addVar e1Out)
          UNot -> pure . Right $ Add (ConstGate 1) (ScalarMul (-1) (addVar e1Out))
  EBinOp op e1 e2 -> do
    e1Outs <- fmap addVar <$> compile e1
    e2Outs <- fmap addVar <$> compile e2
    for (NE.zip e1Outs e2Outs) $ \(e1Out, e2Out) ->
      case op of
        BAdd -> pure . Right $ Add e1Out e2Out
        BMul -> do
          tmp1 <- mulToImm (Right e1Out) (Right e2Out)
          pure . Left $ tmp1
        BDiv -> do
          _recip <- imm
          _one <- addWire $ Right $ ConstGate 1
          emit $ Mul e2Out (Var _recip) _one
          out <- imm
          emit $ Mul e1Out (Var _recip) out
          pure $ Left out
        -- SUB(x, y) = x + (-y)
        BSub -> pure  . Right $ Add e1Out (ScalarMul (-1) e2Out)
        BAnd -> do
          tmp1 <- mulToImm (Right e1Out) (Right e2Out)
          pure .  Left $ tmp1
        BOr -> do
          -- OR(input1, input2) = (input1 + input2) - (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure  . Right $ Add (Add e1Out e2Out) (ScalarMul (-1) (Var tmp1))
        BXor -> do
          -- XOR(input1, input2) = (input1 + input2) - 2 * (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure . Right $ Add (Add e1Out e2Out) (ScalarMul (-2) (Var tmp1))
  -- IF(cond, true, false) = (cond*true) + ((!cond) * false)
  EIf cond true false -> do
    condOut <-   addVar . assertSingle <$> compile cond
    trueOuts <- fmap addVar <$> compile true
    falseOuts  <- fmap addVar <$> compile false
    tmp1 <- imm
    for_ trueOuts $ \trueOut -> emit $ Mul condOut trueOut tmp1
    tmp2 <- imm
    for_ falseOuts $ \falseOut -> 
      emit $ Mul (Add (ConstGate 1) (ScalarMul (-1) condOut)) falseOut tmp2
    pure . NE.singleton . Right $ Add (Var tmp1) (Var tmp2)
  -- EQ(lhs, rhs) = (lhs - rhs == 1) only allowed for field comparison
  EEq lhs rhs -> NE.singleton <$> do
    lhsSubRhs <- assertSingle <$> compile (EBinOp BSub lhs rhs)
    eqInWire <- addWire lhsSubRhs
    eqFreeWire <- imm
    eqOutWire <- imm
    emit $ Equal eqInWire eqFreeWire eqOutWire
    -- eqOutWire == 0 if lhs == rhs, so we need to return 1 -
    -- neqOutWire instead.
    pure . Right $ Add (ConstGate 1) (ScalarMul (-1) (Var eqOutWire))

  ESplit input -> do
    i <- compile input >>= addWire . assertSingle
    outputs <- traverse (const $ mkBoolVar =<< imm) $ universe @(NBits f)
    emit $ Split i (V.toList outputs)
    traverse (fmap assertSingle . compile . EVar . VarBool) (NE.fromList . V.toList $ outputs)
    where
      mkBoolVar w = do
        squared <- mulToImm (Left w) (Left w)
        emit $ Mul (Var squared) (ConstGate 1) w
        pure w
  EBundle as -> do 
      as' <- traverse compile as
      pure $ Prelude.foldl1 (<>) (toList as')
  EJoin bits -> NE.singleton <$> do
    bs <- toList <$> compile bits
    ws <- traverse addWire bs
    pure . Right $ unsplit ws
  EAtIndex v _ix -> NE.singleton <$> do
    v' <- compile v
    pure $ v' NE.!! (fromIntegral _ix)
  EUpdateIndex p b v -> do
    v' <- compile v
    b' <- assertSingle <$> compile b
    pure $ v' & ix (fromIntegral p) .~ b'

exprToArithCircuit ::
  (Num f) =>
  -- \| expression to compile
  Expr Wire f ty ->
  -- | Wire to assign the output of the expression to
  Wire ->
  ExprM f ()
exprToArithCircuit expr output = do
  exprOut <- assertSingle <$> compile expr
  emit $ Mul (ConstGate 1) (addVar exprOut) output

instance (GaloisField f) => Semiring (Expr Wire f  f) where
  plus = EBinOp BAdd
  zero = EVal $ ValField 0
  times = EBinOp BMul
  one = EVal $ ValField 1

instance (GaloisField f) => Ring (Expr Wire f  f) where
  negate = EUnOp UNeg

instance (GaloisField f) => Num (Expr Wire f  f) where
  (+) = plus
  (*) = times
  (-) = EBinOp BSub
  negate = EUnOp UNeg
  abs = identity
  signum = const 1
  fromInteger = EVal . ValField . fromInteger

universe :: (KnownNat n) => Vector n (Finite n)
universe = V.enumFromN 0