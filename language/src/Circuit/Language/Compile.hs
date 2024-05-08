{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

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
import Circuit.Language.Expr
import Data.Field.Galois (GaloisField)
import Data.IntSet qualified as IntSet
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import Data.Sequence (pattern (:|>))
import Data.Vector qualified as V
import Data.Vector.Sized qualified as SV
import Protolude hiding (Semiring)
import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)
import Lens.Micro ((.~), ix)
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
  | MissingCacheKey Hash

instance (GaloisField f) => Pretty (CircuitBuilderError f) where
  pretty = \case
    ExpectedSingleWire wires -> "Expected a single wire, but got:" <+> pretty (toList wires)
    MismatchedWireTypes l r -> "Mismatched wire types:" <+> pretty (toList l) <+> pretty (toList r)
    MissingCacheKey h -> "Missing cache key:" <+> pretty @Text (show h)

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
      { bsVars = (bsVars s) {cvVars = IntSet.insert v (cvVars $ bsVars s)},
        bsNextVar = v + 1
      }
  pure v
{-# INLINE fresh #-}

-- | Fresh intermediate variables
imm :: (MonadState (BuilderState f) m) => m Wire
imm = IntermediateWire <$> fresh
{-# INLINE imm #-}

-- | Fresh input variables
freshPublicInput :: (MonadState (BuilderState f) m) => Text -> m Wire
freshPublicInput label = do
  v <- InputWire label Public <$> fresh
  modify $ \s ->
    s
      { bsVars =
          (bsVars s)
            { cvPublicInputs = IntSet.insert (wireName v) (cvPublicInputs $ bsVars s),
              cvInputsLabels = insertInputBinding label (wireName v) (cvInputsLabels $ bsVars s)
            }
      }
  pure v
{-# INLINE freshPublicInput #-}

freshPrivateInput :: (MonadState (BuilderState f) m) => Text -> m Wire
freshPrivateInput label = do
  v <- InputWire label Private <$> fresh
  modify $ \s ->
    s
      { bsVars =
          (bsVars s)
            { cvPrivateInputs = IntSet.insert (wireName v) (cvPrivateInputs $ bsVars s),
              cvInputsLabels = insertInputBinding label (wireName v) (cvInputsLabels $ bsVars s)
            }
      }
  pure v
{-# INLINE freshPrivateInput #-}

-- | Fresh output variables
freshOutput :: (MonadState (BuilderState f) m) => Text -> m Wire
freshOutput label = do
  v <- OutputWire <$> fresh
  modify $ \s ->
    s
      { bsVars =
          (bsVars s)
            { cvOutputs = IntSet.insert (wireName v) (cvOutputs $ bsVars s),
              cvInputsLabels = insertInputBinding label (wireName v) (cvInputsLabels $ bsVars s)
            }
      }
  pure v
{-# INLINE freshOutput #-}

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
{-# INLINE mulToImm #-}

-- | Add a Mul and its output to the ArithCircuit
emit :: (MonadState (BuilderState f) m) => Gate f Wire -> m ()
emit c = modify $ \s@(BuilderState {bsCircuit = ArithCircuit cs}) ->
  s {bsCircuit = ArithCircuit (c : cs)}
{-# INLINE emit #-}

-- | Turn a wire into an affine circuit, or leave it be
addVar :: SignalSource f -> AffineCircuit f Wire
addVar s = case s of
  WireSource w -> Var w
  AffineSource c -> c
{-# INLINE addVar #-}

-- | Turn an affine circuit into a wire, or leave it be
addWire :: (MonadState (BuilderState f) m, Num f) => SignalSource f -> m Wire
addWire x = case x of
  WireSource w -> pure w
  AffineSource c -> do
    mulOut <- imm
    emit $ Mul (ConstGate 1) c mulOut
    pure mulOut
{-# INLINE addWire #-}

--------------------------------------------------------------------------------

compileWithWire ::
  (Hashable f) =>
  (GaloisField f) =>
  Var Wire f 'TField ->
  Expr Wire f 'TField ->
  ExprM f (Var Wire f 'TField)
compileWithWire freshWire e = do
  res <- compileWithWires (V.singleton freshWire) e
  pure . V.head $ res

compileWithWires ::
  (Hashable f) =>
  (GaloisField f) =>
  V.Vector (Var Wire f 'TField) ->
  Expr Wire f ty ->
  ExprM f (V.Vector (Var Wire f 'TField))
compileWithWires ws expr = do
  compileOut <- compile expr
  for (V.zip compileOut ws) $ \(o, freshWire) -> do
    case o of
      WireSource wire -> do
        let wire' = rawWire freshWire
        emit $ Mul (ConstGate 1) (Var wire) wire'
        pure $ VarField wire
      AffineSource circ -> do
        let wire = rawWire freshWire
        emit $ Mul (ConstGate 1) circ wire
        pure $ VarField wire

{-# SCC compile #-}
compile ::
  (Hashable f, GaloisField f) =>
  Expr Wire f ty ->
  ExprM f (V.Vector (SignalSource f))
compile e = do
  case reifyGraph e of
    (xs :|> x) ->
      traverse_ _compile xs >> _compile x
    _ -> panic "empty graph"

{-# SCC _compile #-}
_compile ::
  forall f.
  (Hashable f, GaloisField f) =>
  (Hash, Node Wire f) ->
  ExprM f (V.Vector (SignalSource f))
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
    source <- case op of
          UURot n ->
            pure $ V.fromList $ rotateList n (toList eOuts)
          UUShift n -> do
            let f = NVal 0 :: Node Wire f
            _f <- _compile (Hash $ hash f, f) >>= assertSingleSource
            pure $ V.fromList $ shiftList _f n (toList eOuts)
          _ -> let f eOut = case op of
                     UUNeg -> AffineSource $ ScalarMul (-1) (addVar eOut)
                     UUNot -> AffineSource $ Add (ConstGate 1) (ScalarMul (-1) (addVar eOut))
                in pure $ map f eOuts
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
    source <-
      fold
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
  NAtIndex a idx -> do
    bs <- assertFromCache a
    o <- addWire $ bs V.! idx
    let source = V.singleton . WireSource $ o
    cachResult h source
    pure source
  NUpdateAtIndex a idx v -> do
    bs <- assertFromCache a
    v' <- assertFromCache v >>= assertSingleSource
    let source = V.fromList $ (toList bs) & ix idx .~ v'
    cachResult h source
    pure source
  where
    cachResult i ws = modify $ \s ->
      s {bsMemoMap = Map.insert i ws (bsMemoMap s)}

    assertFromCache i = do
      m <- gets bsMemoMap
      case Map.lookup i m of
        Just ws -> pure ws
        Nothing -> throwError $ MissingCacheKey i
    {-# INLINE assertFromCache #-}

    assertSameSourceSize l r =
      unless (V.length l == V.length r) $
        throwError $
          MismatchedWireTypes l r
    {-# INLINE assertSameSourceSize #-}

assertSingleSource ::
  (MonadError (CircuitBuilderError f) m) =>
  V.Vector (SignalSource f) ->
  m (SignalSource f)
assertSingleSource xs = case xs V.!? 0 of
  Just x -> pure x
  _ -> throwError $ ExpectedSingleWire xs
{-# INLINE assertSingleSource #-}

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
  Expr Wire f 'TField ->
  ExprM f (Expr Wire f 'TBool)
fieldToBool e = do
  -- let eOut = unType e
  a <- compile e >>= assertSingleSource >>= addWire
  emit $ Boolean a
  pure $ unsafeCoerce e

_unBundle ::
  forall n f ty.
  (KnownNat n) =>
  (GaloisField f) =>
  (Hashable f) =>
  Expr Wire f (TVec n ty) ->
  ExprM f (SV.Vector n (Expr Wire f 'TField))
_unBundle b = do
  bis <- compile b
  ws <- traverse addWire bis
  pure $ fromJust $ SV.toSized (var_ . VarField <$> ws)
