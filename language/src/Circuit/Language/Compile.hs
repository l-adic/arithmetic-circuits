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

-------------------------------------------------------------------------------
-- Circuit Builder
-------------------------------------------------------------------------------

data BuilderState f = BuilderState
  { bsCircuit :: ArithCircuit f,
    bsNextVar :: Int,
    bsVars :: CircuitVars Text,
    bsMemoMap :: Map Hash (V.Vector (SignalSource f))
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
compile e = do
  let g = reifyGraph e
  go g
  where
    go [] = panic "empty graph"
    go [x] = _compile x
    go (x : xs) = _compile x >> go xs

_compile ::
  forall f m.
  (Hashable f, GaloisField f) =>
  (MonadState (BuilderState f) m) =>
  (MonadError (CircuitBuilderError f) m) =>
  (Hash, Node Wire f) ->
  m (V.Vector (SignalSource f))
_compile (h, expr) = case expr of
  NVal f -> do
    let source = V.singleton $ AffineSource $ ConstGate f
    cachResult h source
    pure source
  NVar v -> do
    let source = V.singleton $ WireSource v
    cachResult h source
    pure source 
  NUnOp op e -> do
    eOuts <- assertFromCache e
    let f eOut = case op of
          UUNeg -> AffineSource $ ScalarMul (-1) (addVar eOut)
          UUNot -> AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (addVar eOut))
        source = map f eOuts
    cachResult h source
    pure source
  NBinOp op e1 e2 -> do
    e1Outs <- assertFromCache e1
    e2Outs <- assertFromCache e2
    assertSameSourceSize e1Outs e2Outs
    source <- for (V.zip (addVar <$> e1Outs) (addVar <$> e2Outs)) $ \(e1Out, e2Out) ->
      case op of
        UBAdd -> pure . AffineSource $ Add e1Out e2Out
        UBMul -> do
          tmp1 <- mulToImm (AffineSource e1Out) (AffineSource e2Out)
          pure . WireSource $ tmp1
        UBDiv -> do
          _recip <- imm
          _one <- addWire $ AffineSource $ ConstGate 1
          emit $ Mul e2Out (Var _recip) _one
          out <- imm
          emit $ Mul e1Out (Var _recip) out
          pure $ WireSource out
        -- SUB(x, y) = x + (-y)
        UBSub -> pure . AffineSource $ Add e1Out (ScalarMul (-1) e2Out)
        UBAnd -> do
          tmp1 <- mulToImm (AffineSource e1Out) (AffineSource e2Out)
          pure . WireSource $ tmp1
        UBOr -> do
          -- OR(input1, input2) = (input1 + input2) - (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure . AffineSource $ Add (Add e1Out e2Out) (ScalarMul (-1) (Var tmp1))
        UBXor -> do
          -- XOR(input1, input2) = (input1 + input2) - 2 * (input1 * input2)
          tmp1 <- imm
          emit $ Mul e1Out e2Out tmp1
          pure . AffineSource $ Add (Add e1Out e2Out) (ScalarMul (-2) (Var tmp1))
    cachResult h source
    pure source

  NIf cond true false -> do
    condOut <- addVar <$> (assertFromCache cond >>= assertSingleSource)
    trueOuts <- assertFromCache true
    falseOuts <- assertFromCache false
    assertSameSourceSize trueOuts falseOuts
    tmp1 <- imm
    for_ (addVar <$> trueOuts) $ \trueOut ->
      emit $ Mul condOut trueOut tmp1
    tmp2 <- imm
    for_ (addVar <$> falseOuts) $ \falseOut ->
      emit $ Mul (Add (ConstGate 1) (ScalarMul (-1) condOut)) falseOut tmp2
    let source = V.singleton . AffineSource $ Add (Var tmp1) (Var tmp2)
    cachResult h source
    pure source

  NEq lhs rhs -> do
    let e = NBinOp UBSub lhs rhs
    eqInWire <- do
      eOut <- _compile (Hash $ hash e, e)
      assertSingleSource eOut >>= addWire
    eqFreeWire <- imm
    eqOutWire <- imm
    emit $ Equal eqInWire eqFreeWire eqOutWire
    emit $ Boolean eqOutWire
    -- eqOutWire == 0 if lhs == rhs, so we need to return 1 -
    -- neqOutWire instead.
    let source = V.singleton . AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (Var eqOutWire))
    cachResult h source
    pure source

  NSplit input n -> do
    i <- assertFromCache input >>= assertSingleSource >>= addWire
    outputs <- V.generateM n $ \_ -> do
      w <- imm
      emit $ Boolean w
      pure w
    emit $ Split i (V.toList outputs)
    source <- fold
      <$> for
        outputs
        ( \o -> do
            -- TODO this is kind of a hack
            let e = NVar o
            res <- _compile (Hash $ hash e, e)
            pure res
        )
    cachResult h source
    pure source
  NBundle as -> do
    source <- fold <$> traverse assertFromCache as
    cachResult h source
    pure source

  NJoin bits -> do
    bs <- toList <$> assertFromCache bits
    ws <- traverse addWire bs
    pure . V.singleton . AffineSource $ unsplit ws
  where
    cachResult :: Hash -> V.Vector (SignalSource f) -> m ()
    cachResult i ws = modify $ \s -> s {bsMemoMap = Map.insert i ws (bsMemoMap s)}
    assertFromCache :: Hash -> m (V.Vector (SignalSource f))
    assertFromCache i = do
      m <- gets bsMemoMap
      case Map.lookup i m of
        Just ws -> pure ws
        Nothing -> panic $ "assertFromCache failed on key " <> show i

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
  pure $ fromJust $ SV.toSized (var_ . VarField <$> ws)