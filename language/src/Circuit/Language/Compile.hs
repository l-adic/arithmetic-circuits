module Circuit.Language.Compile
  ( ExprM,
    BuilderState (..),
    execCircuitBuilder,
    evalCircuitBuilder,
    runCircuitBuilder,
    freshPublicInput,
    freshPrivateInput,
    freshOutput,
    imm,
    fieldToBool,
    compileWithWire,
    compileWithWires,
    exprToArithCircuit,
    _unBundle,
  )
where

import Circuit.Affine
import Circuit.Arithmetic
import Circuit.Language.TExpr
import Data.Field.Galois (GaloisField)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Data.Set qualified as Set
import Data.Vector qualified as V
import Data.Vector.Sized qualified as SV
import Protolude hiding (Semiring)
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.Cont (ContT (runContT))

-------------------------------------------------------------------------------
-- Circuit Builder
-------------------------------------------------------------------------------

data BuilderState f = BuilderState
  { bsCircuit :: ArithCircuit f,
    bsNextVar :: Int,
    bsVars :: CircuitVars Text,
    bsMemoMap :: Map Int (V.Vector (SignalSource f))
  }

defaultBuilderState :: BuilderState f
defaultBuilderState =
  BuilderState
    { bsCircuit = ArithCircuit [],
      bsNextVar = 1,
      bsVars = mempty,
      bsMemoMap = mempty
    }

-- non recoverable errors that can arise during circuit building
data CircuitBuilderError f
  = ExpectedSingleWire (V.Vector (SignalSource f))
  | MismatchedWireTypes (V.Vector (SignalSource f)) (V.Vector (SignalSource f))

instance (GaloisField f) => Pretty (CircuitBuilderError f) where
  pretty = \case
    ExpectedSingleWire wires -> "Expected a single wire, but got:" <+> pretty (toList wires)
    MismatchedWireTypes l r -> "Mismatched wire types:" <+> pretty (toList l) <+> pretty (toList r)

type ExprM f a = ExceptT (CircuitBuilderError f) (State (BuilderState f)) a

runExprM :: (GaloisField f) => ExprM f a -> BuilderState f -> (a, BuilderState f)
runExprM m s = do
  let res = runState (runExceptT m) s
  case res of
    (Left e, _) -> panic $ Protolude.show $ pretty e
    (Right a, s') -> (a, s')

execCircuitBuilder :: (GaloisField f) => ExprM f a -> (ArithCircuit f)
execCircuitBuilder m = reverseCircuit . bsCircuit . snd $ runExprM m defaultBuilderState
  where
    reverseCircuit = \(ArithCircuit cs) -> ArithCircuit $ reverse cs

evalCircuitBuilder :: (GaloisField f) => ExprM f a -> a
evalCircuitBuilder e = fst $ runCircuitBuilder e

runCircuitBuilder :: (GaloisField f) => ExprM f a -> (a, BuilderState f)
runCircuitBuilder m = do
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

--------------------------------------------------------------------------------

-- This allows for an optimization to avoid creating a new variable/constraint in the event that
-- the output of an expression is already a wire
data SignalSource f
  = WireSource Wire
  | AffineSource (AffineCircuit f Wire)
  deriving (Show)

instance (Pretty f) => Pretty (SignalSource f) where
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

--------------------------------------------------------------------------------

compileWithWire ::
  (Hashable f) =>
  (GaloisField f) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  m (Var Wire f ty) ->
  Expr Wire f ty ->
  m (Var Wire f ty)
compileWithWire freshWire e = do
  unsafeCoerceGroundType . V.head
    <$> compileWithWires (V.singleton . coerceGroundType <$> freshWire) e

compileWithWires ::
  (Hashable f) =>
  (GaloisField f) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  m (V.Vector (Var Wire f f)) ->
  Expr Wire f ty ->
  m (V.Vector (Var Wire f f))
compileWithWires ws expr = do
  --let e = unType expr
  compileOut <- compile expr
  _ws <- ws
  for (V.zip compileOut _ws) $ \(o, freshWire) -> do
    case o of
      WireSource wire -> do
        let wire' = rawWire freshWire
        emit $ Mul (ConstGate 1) (Var wire') wire
        pure $ VarField wire
      AffineSource circ -> do
        let wire = rawWire freshWire
        emit $ Mul (ConstGate 1) circ wire
        pure $ VarField wire

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

compile :: (Hashable f, GaloisField f) 
  => (MonadState (BuilderState f) m)
  => (MonadError (CircuitBuilderError f) m)
  => Expr Wire f ty -> 
     m (V.Vector (SignalSource f))
compile e = runContT (_compile e) pure

_compile ::
  forall f r m ty.
  (Hashable f, GaloisField f) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  Expr Wire f ty ->
  ContT r m (V.Vector (SignalSource f))
_compile expr = withCompilerCache (getId expr) $ case expr of
  EVal _ f -> pure $ V.singleton $ AffineSource $ ConstGate (rawVal f)
  EVar _ v -> pure . V.singleton $ WireSource (rawWire v)
  EUnOp _ op e1 -> do
    e1Outs <- memoizedCompile e1
    for e1Outs $ \e1Out ->
      case op of
        UNeg -> pure . AffineSource $ ScalarMul (-1) (addVar e1Out)
        UNot -> pure . AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (addVar e1Out))
  EBinOp _ op e1 e2 -> do
    e1Outs <- memoizedCompile e1
    e2Outs <- memoizedCompile e2
    lift $ assertSameSourceSize e1Outs e2Outs
    for (V.zip (addVar <$> e1Outs) (addVar <$> e2Outs)) $ \(e1Out, e2Out) ->
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
  EIf _ cond true false -> do
    condOut <- addVar <$> (memoizedCompile cond >>= lift . assertSingleSource)
    trueOuts <- memoizedCompile true
    falseOuts <- memoizedCompile false
    lift $ assertSameSourceSize trueOuts falseOuts
    tmp1 <- imm
    for_ (addVar <$> trueOuts) $ \trueOut ->
      emit $ Mul condOut trueOut tmp1
    tmp2 <- imm
    for_ (addVar <$> falseOuts) $ \falseOut ->
      emit $ Mul (Add (ConstGate 1) (ScalarMul (-1) condOut)) falseOut tmp2
    pure . V.singleton . AffineSource $ Add (Var tmp1) (Var tmp2)
  -- EQ(lhs, rhs) = (lhs - rhs == 1) only allowed for field comparison
  EEq _ lhs rhs -> do
    -- assertSingle is justified as the lhs and rhs must be of type f
    let h = hash (BSub, getId lhs, getId rhs)
        e = EBinOp h BSub lhs rhs
    eqInWire <- do
      eOut <- withCompilerCache h (memoizedCompile e)
      lift (assertSingleSource eOut) >>= addWire
    eqFreeWire <- imm
    eqOutWire <- imm
    emit $ Equal eqInWire eqFreeWire eqOutWire
    emit $ Boolean eqOutWire
    -- eqOutWire == 0 if lhs == rhs, so we need to return 1 -
    -- neqOutWire instead.
    pure . V.singleton . AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (Var eqOutWire))
  ESplit _ input -> do
    let n = fromIntegral $ natVal (Proxy @(NBits f))
    -- assertSingle is justified as the input must be of type f
    i <- memoizedCompile input >>= lift . assertSingleSource >>= addWire
    outputs <- V.generateM n $ \_ -> do
      w <- imm
      emit $ Boolean w
      pure w
    emit $ Split i (V.toList outputs)
    fold
      <$> for
        outputs
        ( \o ->
            let v = VarBool o
                h = hash v
                e = EVar h v
             in memoizedCompile e
        )
  EBundle _ as -> do
    as' <- traverse memoizedCompile as
    pure $ fold as'
  EJoin _ bits -> do
    bs <- toList <$> memoizedCompile bits
    ws <- traverse addWire bs
    pure . V.singleton . AffineSource $ unsplit ws
  where
    withCompilerCache i m = do
      res <- m
      modify $ \s -> s {bsMemoMap = Map.insert i res (bsMemoMap s)}
      pure res

    memoizedCompile e = do
      m <- gets bsMemoMap
      case Map.lookup (getId e) m of
        Just ws -> pure ws
        Nothing -> _compile e

exprToArithCircuit ::
  (Hashable f, GaloisField f) =>
  -- \| expression to compile
  Expr Wire f ty ->
  -- | Wire to assign the output of the expression to
  Wire ->
  ExprM f ()
exprToArithCircuit expr output = do
  -- let e =  unType expr
  compileOut <- compile expr >>= assertSingleSource
  emit $ Mul (ConstGate 1) (addVar compileOut) output

fieldToBool ::
  (Hashable f, GaloisField f) =>
  Expr Wire f f ->
  ExprM f (Expr Wire f Bool)
fieldToBool e = do
  --let eOut = unType e
  a <- compile e >>= assertSingleSource >>= addWire
  emit $ Boolean a
  pure $ unsafeCoerce e


_unBundle ::
  forall n f ty.
  (KnownNat n) =>
  (GaloisField f) =>
  (Hashable f) =>
  Expr Wire f (SV.Vector n ty) ->
  ExprM f (SV.Vector n (Expr Wire f f))
_unBundle b = do
  bis <- compile  b
  ws <- traverse addWire bis
  pure $ fromJust $ SV.toSized (var . VarField <$> ws)