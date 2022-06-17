{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Symbolic.Eval
  ( -- * Runners

    -- ** General inputs and outputs
    AvailableFuel (..),
    Path (..),
    PathStatus (..),

    -- ** Base symbolic evaluation
    SymEvalStatistics (..),

    -- ** Incorrectness logic
    symevalAnyPath,
    symEvalMatchesFirst,
    UniversalAxiom (..),
    Model (..),

    -- * Re-export types
    module X,

    -- * Internal, used to build on top of 'SymEvalT'
    SymEvalConstr,
    SymEvalT,
    symevalT,
    runSymEvalT,
    declSymVars,
    learn,
    prune,
    symEvalOneStep,
    pruneAndValidate,
    PruneResult (..),
    SymEvalSt (..),
    currentStatistics,
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.List (genericLength)
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import ListT.Weighted (WeightedListT)
import qualified ListT.Weighted as ListT
import Pirouette.Monad
import Pirouette.Monad.Maybe
import Pirouette.Symbolic.Eval.SMT
import qualified Pirouette.SMT.Constraints as C
import qualified Pirouette.SMT.FromTerm as Tr
import qualified Pirouette.SMT.Monadic as SMT
import Pirouette.Symbolic.Eval.Types as X
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import qualified PureSMT

-- | A 'SymEvalT' is equivalent to a function with type:
--
-- > SymEvalSt lang -> SMT.Solver -> m [(a, SymEvalSt lang)]
newtype SymEvalT lang m a = SymEvalT {symEvalT :: StateT (SymEvalSt lang) (SMT.SolverT (WeightedListT m)) a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadState (SymEvalSt lang), ListT.MonadWeightedList)

deriving instance PirouetteReadDefs lang m => PirouetteReadDefs lang (SymEvalT lang m)

deriving instance MonadError e m => MonadError e (SymEvalT lang m)

type SymEvalConstr lang m =
  (PirouetteDepOrder lang m, LanguagePretty lang, LanguageSymEval lang, MonadFail m, MonadIO m)

symevalT ::
  (SymEvalConstr lang m) =>
  StoppingCondition ->
  SymEvalT lang m a ->
  m [Path lang a]
symevalT shouldStop = runSymEvalT st0
  where
    st0 = SymEvalSt mempty M.empty 0 mempty False S.empty shouldStop

symevalAnyPath ::
  (SymEvalConstr lang m) =>
  StoppingCondition ->
  (Path lang a -> Bool) ->
  SymEvalT lang m a ->
  m (Maybe (Path lang a))
symevalAnyPath shouldStop p =
  ListT.firstThat p . runSymEvalTWorker st0
  where
    st0 = SymEvalSt mempty M.empty 0 mempty False S.empty shouldStop

runSymEvalTRaw ::
  (Monad m) =>
  SymEvalSt lang ->
  SymEvalT lang m a ->
  SMT.SolverT (WeightedListT m) (a, SymEvalSt lang)
runSymEvalTRaw st = flip runStateT st . symEvalT

-- | Running a symbolic execution will prepare the solver only once, then use a persistent session
--  to make all the necessary queries.
runSymEvalT ::
  (SymEvalConstr lang m) =>
  SymEvalSt lang ->
  SymEvalT lang m a ->
  m [Path lang a]
runSymEvalT st = ListT.toList . runSymEvalTWorker st

-- | Running a symbolic execution will prepare the solver only once, then use a persistent session
--  to make all the necessary queries.
runSymEvalTWorker ::
  forall lang m a.
  (SymEvalConstr lang m) =>
  SymEvalSt lang ->
  SymEvalT lang m a ->
  WeightedListT m (Path lang a)
runSymEvalTWorker st f = do
  ctx <- lift prepSolver
  solvPair <- SMT.runSolverT s $ do
    solver <- ask
    liftIO $ PureSMT.initSolver ctx solver
    let newState = st {sestKnownNames = solverSharedCtxUsedNames ctx `S.union` sestKnownNames st}
    runSymEvalTRaw newState f
  let paths = uncurry path solvPair
  return paths
  where
    -- we'll rely on cvc4 with dbg messages
    -- s = SMT.cvc4_ALL_SUPPORTED True
    -- no debug messages
    s = SMT.cvc4_ALL_SUPPORTED False

    lkupTypeDefOf decls name = case M.lookup name decls of
      Just (DTypeDef tdef) -> Just (name, tdef)
      _ -> Nothing

    lkupFunDefOf decls name = case M.lookup name decls of
      Just (DFunDef fdef) -> Just (name, fdef)
      _ -> Nothing

    prepSolver :: m (SolverSharedCtx lang)
    prepSolver = do
      decls <- prtAllDefs
      dependencyOrder <- prtDependencyOrder
      let types = mapMaybe (R.argElim (lkupTypeDefOf decls) (const Nothing)) dependencyOrder
      let allFns = mapMaybe (R.argElim (const Nothing) (lkupFunDefOf decls)) dependencyOrder
      let fns = mapMaybe (\(n, fd) -> (n,) <$> SMT.supportedUninterpretedFunction fd) allFns
      return $ SolverSharedCtx types fns

instance (Monad m) => Alternative (SymEvalT lang m) where
  empty = SymEvalT $ StateT $ const empty
  xs <|> ys = SymEvalT $ StateT $ \st -> runSymEvalTRaw st xs <|> runSymEvalTRaw st ys

instance MonadTrans (SymEvalT lang) where
  lift = SymEvalT . lift . lift . lift

instance (MonadFail m) => MonadFail (SymEvalT lang m) where
  fail = lift . fail

instance (MonadIO m) => MonadIO (SymEvalT lang m) where
  liftIO = lift . liftIO

-- | Prune the set of paths in the current set.
prune :: forall lang m a. (SymEvalConstr lang m) => SymEvalT lang m a -> SymEvalT lang m a
prune xs = SymEvalT $
  StateT $ \st -> do
    (x, st') <- runSymEvalTRaw st xs
    -- trace ("  X is " ++ show (pretty x)) $ return ()
    -- trace ("  in the context " ++ show (pretty st')) $ return ()
    solver <- ask
    defs <- lift $ lift getPrtOrderedDefs
    ok <- liftIO $ PureSMT.solveProblem (CheckPath $ CheckPathProblem st' defs) solver
    guard ok
    return (x, st')

-- | Learn a new constraint and add it as a conjunct to the set of constraints of
--  the current path. Make sure that this branch gets marked as /not/ validated, regardless
--  of whether or not we had already validated it before.
learn :: (SymEvalConstr lang m) => Constraint lang -> SymEvalT lang m ()
learn c = modify (\st -> st {sestConstraint = c <> sestConstraint st, sestValidated = False})

declSymVars :: (SymEvalConstr lang m) => [(Name, Type lang)] -> SymEvalT lang m [SymVar]
declSymVars vs = do
  modify (\st -> st {sestGamma = M.union (sestGamma st) (M.fromList vs)})
  return $ map (SymVar . fst) vs

-- freshSymVar :: (SymEvalConstr lang m) => Type lang -> SymEvalT lang m SymVar
-- freshSymVar ty = head <$> freshSymVars [ty]

freshSymVars :: (SymEvalConstr lang m) => [Type lang] -> SymEvalT lang m [SymVar]
freshSymVars [] = return []
freshSymVars tys = do
  let n = length tys
  ctr <- gets sestFreshCounter
  modify (\st -> st {sestFreshCounter = sestFreshCounter st + n})
  let vars = zipWith (\i ty -> (Name "s" (Just i), ty)) [ctr ..] tys
  declSymVars vars

currentStatistics :: (SymEvalConstr lang m) => SymEvalT lang m SymEvalStatistics
currentStatistics = gets sestStatistics

-- | Take one step of evaluation.
-- We wrap everything in an additional 'Writer' which tells us
-- whether a step was taken at all.
symEvalOneStep ::
  forall lang m.
  (SymEvalConstr lang m, PirouetteReadDefs lang m) =>
  TermMeta lang SymVar ->
  WriterT Any (SymEvalT lang m) (TermMeta lang SymVar)
-- We cannot symbolic-evaluate polymorphic terms
symEvalOneStep R.Abs {} = error "Can't symbolically evaluate polymorphic things"
-- If we're forced to symbolic evaluate a lambda, we create a new metavariable
-- and evaluate the corresponding application.
symEvalOneStep t@(R.Lam (R.Ann _x) _ty _) = do
  {-
  Note that our AST only represents terms in normal form,
  so it cannot be the case that we have:
  > App (Lam ...) ...
  So beta-reduction does not enter the game here.
  We have two options at this point:
  -}
  {-
  # option 1: evaluate under lambda

  This can give us a bit of better results, but in most cases it seems
  to win us nothing. For example, if we are evaluating:
  > map (\x -> x + 1) l
  then going into (\x -> x + 1) would only lead to reconstructing it,
  the real work happens on the definition of 'map'.
  We have decided to *not* go under lambdas, but here's the implementation
  in case we need it in the future.
  -}
  {-
  let ty' = typeFromMeta ty
  [svars] <- declSymVars [(x, ty')]
  body <- symEvalOneStep (t `R.app` R.TermArg (R.App (R.Meta svars) []))
  pure $ R.Lam (R.Ann x) ty body
  -}
  {-
  # option 2: do nothing to lambdas
  -}
  pure t
-- If we're evaluating an application, we distinguish between a number
-- of constituent cases:
symEvalOneStep t@(R.App hd args) = case hd of
  R.Free (Builtin builtin) -> do
    -- try to evaluate the built-in
    let translator c = do
          c' <- Tr.runTranslator $ Tr.translateTerm S.empty c
          case c' of
            Left _ -> pure Nothing
            Right (d, _) -> pure $ Just d
    mayBranches <- lift $ branchesBuiltinTerm @lang builtin translator args
    case mayBranches of
      -- if successful, open all the branches
      Just branches -> asum $
        flip map branches $ \(SMT.Branch additionalInfo newTerm) -> do
          lift $ learn additionalInfo
          consumeFuel
          signalEvaluation
          pure newTerm
      -- if it's not ready, just keep evaluating the arguments
      Nothing -> justEvaluateArgs
  R.Free (TermSig n) -> do
    mDefHead <- Just <$> lift (lift $ prtDefOf n)
    case mDefHead of
      -- If hd is not defined, we symbolically evaluate the arguments and reconstruct the term.
      Nothing -> justEvaluateArgs
      Just (DTypeDef _) -> error "Can't evaluate typedefs"
      -- If hd is a defined function, we inline its definition and symbolically evaluate
      -- the result consuming one gas.
      Just (DFunction _rec body _) -> do
        consumeFuel
        signalEvaluation
        pure $ termToMeta body `R.appN` args
      Just (DConstructor _ _) -> justEvaluateArgs
      Just (DDestructor tyName) -> symEvalDestructor t tyName
  R.Meta vr -> do
    -- if we have a meta, try to replace it
    cstr <- gets sestConstraint
    case cstr of
      C.And atomics -> do
        let findAssignment v (C.Assign w _) = v == w
            findAssignment _ _ = False
            findEq v (C.VarEq w _) = v == w
            findEq _ _ = False
            -- we need to jump more than one equality,
            -- hence the involved loop here
            findLoop v
              | Just (C.Assign _ tm) <- find (findAssignment v) atomics =
                Just tm
              | Just (C.VarEq _ other) <- find (findEq v) atomics =
                findLoop other
              | otherwise =
                Nothing
        case findLoop vr of
          Nothing -> justEvaluateArgs
          Just lp -> signalEvaluation >> pure lp
      _ -> justEvaluateArgs

  -- in any other case don't try too hard
  _ -> justEvaluateArgs
  where
    justEvaluateArgs =
      R.App hd
        <$> symEvalMatchesFirst
          (\case R.TyArg {} -> Nothing; R.TermArg v -> Just v)
          R.TermArg
          args

-- | Strategy for evaluating a set of expression,
--   but giving priority to destructors over the rest.
--
--   The two functions allow us to inject to and from
--   Term, so we can reuse this function either
--   with Arg (as done above), or with regular Term.
symEvalMatchesFirst ::
  forall lang m a.
  (SymEvalConstr lang m, PirouetteReadDefs lang m) =>
  (a -> Maybe (TermMeta lang SymVar)) ->
  (TermMeta lang SymVar -> a) ->
  [a] ->
  WriterT Any (SymEvalT lang m) [a]
symEvalMatchesFirst f g exprs = go [] exprs
  where
    -- we came to the end without a match,
    -- so we execute one step in parallel
    go _acc [] = forM exprs $ \x -> case f x of
      Nothing -> pure x
      Just t -> g <$> symEvalOneStep t
    -- first pass, only evaluate destructors
    -- the accumulator is used only if we ever
    -- find that match
    go acc (x : xs)
      | Nothing <- f x = go (x : acc) xs
      | Just t <- f x = do
        mayTyName <- lift $ lift $ isDestructor t
        case mayTyName of
          Just tyName -> (reverse acc ++) . (: xs) . g <$> symEvalDestructor t tyName
          Nothing -> go (x : acc) xs

isDestructor ::
  forall lang m.
  (SymEvalConstr lang m, PirouetteReadDefs lang m) =>
  TermMeta lang SymVar ->
  m (Maybe Name)
isDestructor (R.App (R.Free (TermSig n)) _args) = do
  mDefHead <- Just <$> prtDefOf n
  pure $ case mDefHead of
    Just (DDestructor tyName) -> Just tyName
    _ -> Nothing
isDestructor _ = pure Nothing

-- If hd is a destructor, we have more work to do: we have to expand the term
-- being destructed, then combine it with all possible destructor cases.
-- Say we're looking at:
--
-- > symeval (Nil_match @Int l N (\x xs -> M))
--
-- Then say that symeval l == [(c1, Cons sv1 sv2)]; we now create a fresh
-- symbolic variable S to connect the result of l and each of the branches.
-- The overall result should be something like:
--
-- > [ (c1 && S = Cons sv1 sv2 && S = Nil , N)
-- > , (c1 && S = Cons sv1 sv2 && S = Cons sv3 sv4 , M)
-- > ]
--
-- Naturally, the first path is already impossible so we do not need to
-- move on to evaluate N.
symEvalDestructor ::
  forall lang m.
  (SymEvalConstr lang m, PirouetteReadDefs lang m) =>
  TermMeta lang SymVar ->
  Name ->
  WriterT Any (SymEvalT lang m) (TermMeta lang SymVar)
symEvalDestructor t@(R.App hd _args) tyName = do
  Just (UnDestMeta _ _ tyParams term tyRes cases excess) <- lift $ lift $ runMaybeT (unDest t)
  _dt@(Datatype _ _ _ consList) <- lift $ lift $ prtTypeDefOf tyName
  -- We know what is the type of all the possible term results, its whatever
  -- type we're destructing applied to its arguments, making sure it contains
  -- no meta variables.
  (term', somethingWasEvaluated) <- listen $ symEvalOneStep term
  tell somethingWasEvaluated -- just in case
  -- We only do the case distinction if we haven't taken any step
  -- in the previous step. Otherwise it wouldn't be a "one step" evaluator.
  let motiveIsMeta = termIsMeta term'
  motiveWHNF <- lift $ termIsWHNF term'
  let bailOutArgs = R.TermArg term' : R.TyArg tyRes : map R.TermArg cases
      bailOutTerm = R.App hd (map R.TyArg tyParams ++ bailOutArgs ++ excess)
  case (somethingWasEvaluated, motiveIsMeta, motiveWHNF) of
    (Any True, _, _) -> pure bailOutTerm -- we did some evaluation
    (_, Nothing, Nothing) -> pure bailOutTerm -- cannot make progress still
    (_, _, Just WHNFConstant {}) -> pure bailOutTerm -- match and constant is a weird combination
    (_, Just _, _) -> do
      -- we have a meta, explore every possibility
      -- liftIO $ putStrLn $ "DESTRUCTOR " <> show tyName <> " over " <> show term'
      let tyParams' = map typeFromMeta tyParams
      asum $
        for2 consList cases $ \(consName, consTy) caseTerm -> do
          let instantiatedTy = R.tyInstantiateN consTy tyParams'
          let (consArgs, _) = R.tyFunArgs instantiatedTy
          svars <- lift $ freshSymVars consArgs
          let symbArgs = map (R.TermArg . (`R.App` []) . R.Meta) svars
          let symbCons = R.App (R.Free $ TermSig consName) (map (R.TyArg . typeToMeta) tyParams' ++ symbArgs)
          let mconstr = unify term' symbCons
          -- liftIO $ print mconstr
          case mconstr of
            Nothing -> empty
            Just constr -> do
              let countAssigns SMT.Bot = 0
                  countAssigns (SMT.And atomics) = genericLength $ filter isAssign atomics
                  isAssign SMT.Assign {} = True
                  isAssign _ = False
              -- add weight as many new assignments we get from unification
              ListT.weight (countAssigns constr) $ do
                lift $ learn constr
                moreConstructors (countAssigns constr)
                signalEvaluation
                pure $ (caseTerm `R.appN` symbArgs) `R.appN` excess
    (_, _, Just (WHNFConstructor ix _ty constructorArgs)) -> do
      -- we have a particular constructor
      -- liftIO $ putStrLn $ "DESTRUCTOR " <> show ix <> " from type " <> show ty <> " ; " <> show tyName <> " over " <> show term'
      -- liftIO $ putStrLn $ "possibilitites: " <> show (pretty dt)
      let caseTerm = cases !! ix
      -- we do not introduce any new constructors
      signalEvaluation
      pure $ (caseTerm `R.appN` dropWhile R.isTyArg constructorArgs) `R.appN` excess
symEvalDestructor _ _ = error "should never be called with anything else than App"

-- | Indicate that something has been evaluated.
signalEvaluation :: Functor m => WriterT Any (SymEvalT lang m) ()
signalEvaluation = tell (Any True)

-- | Consume one unit of fuel.
-- This also tells the symbolic evaluator that a step was taken.
consumeFuel :: (SymEvalConstr lang m) => WriterT Any (SymEvalT lang m) ()
consumeFuel = do
  modify (\st -> st {sestStatistics = sestStatistics st <> mempty {sestConsumedFuel = 1}})

moreConstructors :: (SymEvalConstr lang m) => Int -> WriterT Any (SymEvalT lang m) ()
moreConstructors n = do
  modify (\st -> st {sestStatistics = sestStatistics st <> mempty {sestConstructors = n}})

unify :: (LanguageBuiltins lang) => TermMeta lang SymVar -> TermMeta lang SymVar -> Maybe (Constraint lang)
unify (R.App (R.Meta s) []) (R.App (R.Meta r) []) = Just (symVarEq s r)
unify (R.App (R.Meta s) []) t = Just (s =:= t)
unify u (R.App (R.Meta s) []) = Just (s =:= u)
unify (R.App hdT argsT) (R.App hdU argsU) = do
  uTU <- unifyVar hdT hdU
  uArgs <- zipWithMPlus unifyArg argsT argsU
  return $ uTU <> mconcat uArgs
unify t u = Just (SMT.And [SMT.NonInlinableSymbolEq t u])

unifyVar :: (LanguageBuiltins lang) => VarMeta lang SymVar -> VarMeta lang SymVar -> Maybe (Constraint lang)
unifyVar (R.Meta s) (R.Meta r) = Just (symVarEq s r)
unifyVar (R.Meta s) t = Just (s =:= R.App t [])
unifyVar t (R.Meta s) = Just (s =:= R.App t [])
unifyVar t u = guard (t == u) >> Just (SMT.And [])

unifyArg :: (LanguageBuiltins lang) => ArgMeta lang SymVar -> ArgMeta lang SymVar -> Maybe (Constraint lang)
unifyArg (R.TermArg x) (R.TermArg y) = unify x y
unifyArg (R.TyArg _) (R.TyArg _) = Just (SMT.And []) -- TODO: unify types too?
unifyArg _ _ = Nothing

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 as bs f = zipWith f as bs

-- | Variation on zipwith that forces arguments to be of the same length,
-- returning 'mzero' whenever that does not hold.
zipWithMPlus :: (MonadPlus m) => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithMPlus _ [] [] = return []
zipWithMPlus _ _ [] = mzero
zipWithMPlus _ [] _ = mzero
zipWithMPlus f (x : xs) (y : ys) = (:) <$> f x y <*> zipWithMPlus f xs ys

-- | Prune the set of paths in the current set.
pruneAndValidate ::
  (SymEvalConstr lang m) =>
  Constraint lang ->
  Maybe (Constraint lang) ->
  [UniversalAxiom lang] ->
  SymEvalT lang m PruneResult
pruneAndValidate cOut cIn axioms =
  SymEvalT $
    StateT $ \st -> do
      solver <- ask
      defs <- lift $ lift getPrtOrderedDefs
      contradictProperty <- liftIO $ PureSMT.solveProblem (CheckProperty $ CheckPropertyProblem cOut cIn axioms st defs) solver
      -- liftIO $ putStrLn $ show (pretty cOut) ++ " => " ++ maybe "--" (show . pretty) cIn ++ "? " ++ show contradictProperty
      return (contradictProperty, st)
