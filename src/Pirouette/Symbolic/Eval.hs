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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Symbolic.Eval
  ( -- * Runners
    symeval,

    -- ** Options
    Options (..),

    -- ** General inputs and outputs
    AvailableFuel (..),
    Path (..),
    PathStatus (..),

    -- ** Base symbolic evaluation
    SymEvalStatistics (..),

    -- ** Incorrectness logic
    symevalAnyPathAccum,
    symEvalMatchesFirst,
    symEvalParallel,
    UniversalAxiom (..),
    Model (..),

    -- * Re-export types
    module X,

    -- * Internal, used to build on top of 'SymEval'
    SymEvalConstr,
    SymEval,
    runSymEval,
    declSymVars,
    learn,
    prune,
    symEvalOneStep,
    pruneAndValidate,
    PruneResult (..),
    SymEvalSt (..),
    SymEvalEnv (..),
    currentStatistics,
  )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Parallel.Strategies
import Data.Default
import Data.Foldable
import Data.List (genericLength)
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import ListT.Weighted (WeightedList)
import qualified ListT.Weighted as ListT
import Pirouette.Monad
import Pirouette.Monad.Maybe
import qualified Pirouette.SMT.Constraints as C
import qualified Pirouette.SMT.FromTerm as Tr
import qualified Pirouette.SMT.Monadic as SMT
import Pirouette.Symbolic.Eval.SMT
import Pirouette.Symbolic.Eval.Types as X
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import qualified PureSMT

data SymEvalSolvers lang = SymEvalSolvers
  { -- | Check whether a path is plausible
    solvePathProblem :: CheckPathProblem lang -> Bool,
    -- | Check whether a certain property currently holds over a given path
    solvePropProblem :: CheckPropertyProblem lang -> PruneResult
  }

data SymEvalEnv lang = SymEvalEnv
  { seeDefs :: PrtOrderedDefs lang,
    seeSolvers :: SymEvalSolvers lang,
    seeOptions :: Options
  }

-- | A 'SymEval' is equivalent to a function with type:
--
-- > SymEvalEnv lang -> SymEvalSt lang -> [(a, SymEvalSt lang)]
newtype SymEval lang a = SymEval
  { symEval ::
      ReaderT
        (SymEvalEnv lang)
        (StateT (SymEvalSt lang) WeightedList)
        a
  }
  deriving (Functor)
  deriving newtype
    ( Applicative,
      Monad,
      MonadReader (SymEvalEnv lang),
      MonadState (SymEvalSt lang),
      ListT.MonadWeightedList
    )

type SymEvalConstr lang = (Language lang, LanguageSymEval lang)

instance (SymEvalConstr lang) => PirouetteReadDefs lang (SymEval lang) where
  prtAllDefs = SymEval (asks $ prtDecls . seeDefs)

instance (SymEvalConstr lang) => PirouetteDepOrder lang (SymEval lang) where
  prtDependencyOrder = SymEval (asks $ prtDepOrder . seeDefs)

instance MonadFail (SymEval lang) where
  fail = error

symeval ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  Options ->
  SymEval lang a ->
  m [Path lang a]
symeval opts prob = do
  defs <- getPrtOrderedDefs
  return $ runSymEval opts defs def prob

symevalAnyPathAccum ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  (Path lang a -> st -> st) ->
  st ->
  Options ->
  (Path lang a -> Bool) ->
  SymEval lang a ->
  m (Maybe (Path lang a), st)
symevalAnyPathAccum f s0 opts p prob = do
  defs <- getPrtOrderedDefs
  return $ runIdentity $ ListT.firstThatAccum f s0 p $ runSymEvalWorker opts defs def prob

-- | Running a symbolic execution will prepare the solver only once, then use a persistent session
--  to make all the necessary queries.
runSymEval ::
  (SymEvalConstr lang) =>
  Options ->
  PrtOrderedDefs lang ->
  SymEvalSt lang ->
  SymEval lang a ->
  [Path lang a]
runSymEval opts defs st = runIdentity . ListT.toList . runSymEvalWorker opts defs st

runSymEvalRaw ::
  (SymEvalConstr lang) =>
  SymEvalEnv lang ->
  SymEvalSt lang ->
  SymEval lang a ->
  WeightedList (a, SymEvalSt lang)
runSymEvalRaw env st act =
  runStateT (runReaderT (symEval act) env) st

-- | Running a symbolic execution will prepare the solver only once, then use a persistent session
--  to make all the necessary queries.
runSymEvalWorker ::
  forall lang a.
  (SymEvalConstr lang) =>
  Options ->
  PrtOrderedDefs lang ->
  SymEvalSt lang ->
  SymEval lang a ->
  WeightedList (Path lang a)
runSymEvalWorker opts defs st f = do
  let -- sharedSolve is here to hint to GHC not to create more than one pool
      -- of SMT solvers, which could happen if sharedSolve were inlined.
      -- TODO: Write a test to check that only one SMT pool is actually created over
      --       multiple calls to runSymEvalWorker.
      {-# NOINLINE sharedSolve #-}
      sharedSolve :: SolverProblem lang res -> res
      sharedSolve = PureSMT.solveOpts (optsPureSMT opts) solverCtx
  let solvers = SymEvalSolvers (sharedSolve . CheckPath) (sharedSolve . CheckProperty)
  let st' = st {sestKnownNames = solverSharedCtxUsedNames solverCtx `S.union` sestKnownNames st}
  solvPair <- runSymEvalRaw (SymEvalEnv defs solvers opts) st' f
  let paths = uncurry (path $ shouldStop opts) solvPair
  return paths
  where
    lkupTypeDefOf decls name = case M.lookup (TypeNamespace, name) decls of
      Just (DTypeDef tdef) -> Just (name, tdef)
      _ -> Nothing

    lkupFunDefOf decls name = case M.lookup (TermNamespace, name) decls of
      Just (DFunDef fdef) -> Just (name, fdef)
      _ -> Nothing

    solverCtx :: SolverSharedCtx lang
    solverCtx =
      let decls = prtDecls defs
          dependencyOrder = prtDepOrder defs
          definedTypes = mapMaybe (R.argElim (lkupTypeDefOf decls) (const Nothing)) dependencyOrder
          allFns = mapMaybe (R.argElim (const Nothing) (lkupFunDefOf decls)) dependencyOrder
          fns = mapMaybe (\(n, fd) -> (n,) <$> SMT.supportedUninterpretedFunction fd) allFns
       in SolverSharedCtx definedTypes fns

instance (SymEvalConstr lang) => Alternative (SymEval lang) where
  empty = SymEval $ ReaderT $ \_ -> StateT $ const empty
  xs <|> ys = SymEval $
    ReaderT $ \env -> StateT $ \st ->
      let (xs', ys') =
            withStrategy
              (parTuple2 rpar rpar)
              (runSymEvalRaw env st xs, runSymEvalRaw env st ys)
       in xs' <|> ys'

-- | Prune the set of paths in the current set.
prune :: forall lang a. (SymEvalConstr lang) => SymEval lang a -> SymEval lang a
prune xs = SymEval $
  ReaderT $ \env -> StateT $ \st ->
    weightedParFilter
      (\(_, st') -> solvePathProblem (seeSolvers env) (CheckPathProblem st' (seeDefs env)))
      (runSymEvalRaw env st xs)

weightedParFilter :: (a -> Bool) -> WeightedList a -> WeightedList a
weightedParFilter _ ListT.Fail = ListT.Fail
weightedParFilter f (ListT.Weight n w) =
  case weightedParFilter f w of
    ListT.Fail -> ListT.Fail
    other -> ListT.Weight n other
weightedParFilter f (ListT.Action (Identity w)) = weightedParFilter f w
weightedParFilter f (ListT.Yield a w) =
  let (keep, rest) =
        withStrategy
          (parTuple2 rpar rpar)
          (f a, weightedParFilter f w)
   in if keep then ListT.Yield a rest else rest

-- | Learn a new constraint and add it as a conjunct to the set of constraints of
--  the current path. Make sure that this branch gets marked as /not/ validated, regardless
--  of whether or not we had already validated it before.
learn :: (SymEvalConstr lang) => [C.Constraint lang SymVar] -> SymEval lang ()
learn cs = do
  curr <- gets sestConstraint
  case foldl' (\mc c -> mc >>= C.conjunct c) (Just curr) cs of
    Just curr' -> modify (\st -> st {sestConstraint = curr'})
    Nothing -> empty

declSymVars :: (SymEvalConstr lang) => [(Name, Type lang)] -> SymEval lang [SymVar]
declSymVars vs = do
  modify (\st -> st {sestGamma = M.union (sestGamma st) (M.fromList vs)})
  return $ map (SymVar . fst) vs

-- freshSymVar :: (SymEvalConstr lang m) => Type lang -> SymEval lang m SymVar
-- freshSymVar ty = head <$> freshSymVars [ty]

freshSymVars :: (SymEvalConstr lang) => [Type lang] -> SymEval lang [SymVar]
freshSymVars [] = return []
freshSymVars tys = do
  let n = length tys
  ctr <- gets sestFreshCounter
  modify (\st -> st {sestFreshCounter = sestFreshCounter st + n})
  let vars = zipWith (\i ty -> (Name "s" (Just i), ty)) [ctr ..] tys
  declSymVars vars

currentStatistics :: (SymEvalConstr lang) => SymEval lang SymEvalStatistics
currentStatistics = gets sestStatistics

-- | Take one step of evaluation.
-- We wrap everything in an additional 'Writer' which tells us
-- whether a step was taken at all.
symEvalOneStep ::
  forall lang.
  (SymEvalConstr lang) =>
  TermMeta lang SymVar ->
  WriterT Any (SymEval lang) (TermMeta lang SymVar)
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
  R.Free Bottom -> empty -- we end in a bottom, so that branch is not useful
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
    mDefHead <- Just <$> lift (prtDefOf TermNamespace n)
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
    case C.expandDefOf cstr vr of
      Nothing -> justEvaluateArgs
      Just valOfvr -> signalEvaluation >> pure valOfvr

  -- in any other case don't try too hard
  _ -> justEvaluateArgs
  where
    justEvaluateArgs =
      R.App hd
        <$> symEvalMatchesFirst
          (\case R.TyArg {} -> Nothing; R.TermArg v -> Just v)
          R.TermArg
          args

-- A-ha... it's the state monad annoying us. Maybe if we can understand whether
-- we really need the state monad we can better understand the parallelism possibilities
-- in here. If we do really need the monad, we can only paralellize the prune and pruneAndValidate
-- functions, if not, we could paralellize everything.
symEvalParallel ::
  forall lang.
  (SymEvalConstr lang) =>
  [TermMeta lang SymVar] ->
  SymEval lang ([TermMeta lang SymVar], Any)
symEvalParallel = runWriterT . mapM symEvalOneStep

-- | Strategy for evaluating a set of expression,
--   but giving priority to destructors over the rest.
--
--   The two functions allow us to inject to and from
--   Term, so we can reuse this function either
--   with Arg (as done above), or with regular Term.
symEvalMatchesFirst ::
  forall lang a.
  (SymEvalConstr lang) =>
  (a -> Maybe (TermMeta lang SymVar)) ->
  (TermMeta lang SymVar -> a) ->
  [a] ->
  WriterT Any (SymEval lang) [a]
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
        mayTyName <- lift $ isDestructor t
        case mayTyName of
          Just tyName -> (reverse acc ++) . (: xs) . g <$> symEvalDestructor t tyName
          Nothing -> go (x : acc) xs

isDestructor ::
  forall lang m.
  (SymEvalConstr lang, PirouetteReadDefs lang m) =>
  TermMeta lang SymVar ->
  m (Maybe Name)
isDestructor (R.App (R.Free (TermSig n)) _args) = do
  mDefHead <- Just <$> prtDefOf TermNamespace n
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
  forall lang.
  (SymEvalConstr lang) =>
  TermMeta lang SymVar ->
  Name ->
  WriterT Any (SymEval lang) (TermMeta lang SymVar)
symEvalDestructor t@(R.App hd _args) tyName = do
  Just (UnDestMeta _ _ tyParams term tyRes cases excess) <- lift $ runMaybeT (unDest t)
  _dt@(Datatype _ _ _ consList) <- lift $ prtTypeDefOf tyName
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
    (_, Just s, _) -> do
      -- we have a meta, explore every possibility
      -- liftIO $ putStrLn $ "DESTRUCTOR " <> show tyName <> " over " <> show term'
      let tyParams' = map typeFromMeta tyParams
      asum $
        -- Here motive is $x and type is, for instance, List Integer.
        -- The next @for2@ will generate all possibilities for $x:
        -- 1. It can be Nil
        -- 2. It can be Cons $y $ys, where $y and $ys are freshly generated symbolic vars
        for2 consList cases $ \(consName, consTy) caseTerm -> do
          -- For consName == "Cons" and consTy == "forall a . a -> List a -> List a", we have:
          -- wlog, assume tyParams' = ["Integer"].
          let instantiatedTy = R.tyInstantiateN consTy tyParams' -- instantiatedTy == "Integer -> List Integer -> List Integer"
          let (consArgs, _) = R.tyFunArgs instantiatedTy -- consArgs == ["Integer", "List Integer"]
          svars <- lift $ freshSymVars consArgs
          let symbArgs = map (R.TermArg . (`R.App` []) . R.Meta) svars
          let symbCons = R.App (R.Free $ TermSig consName) (map (R.TyArg . typeToMeta) tyParams' ++ symbArgs)
          -- We just assigned a value to the motive, hence, by definition, we add one
          -- assignment.
          ListT.weight 1 $ do
            lift $ learn [s C.=:= symbCons]
            moreConstructors 1
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
signalEvaluation :: WriterT Any (SymEval lang) ()
signalEvaluation = tell (Any True)

-- | Consume one unit of fuel.
-- This also tells the symbolic evaluator that a step was taken.
consumeFuel :: (SymEvalConstr lang) => WriterT Any (SymEval lang) ()
consumeFuel = do
  modify (\st -> st {sestStatistics = sestStatistics st <> mempty {sestConsumedFuel = 1}})

moreConstructors :: (SymEvalConstr lang) => Int -> WriterT Any (SymEval lang) ()
moreConstructors n = do
  modify (\st -> st {sestStatistics = sestStatistics st <> mempty {sestConstructors = n}})

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 as bs f = zipWith f as bs

-- | Prune the set of paths in the current set.
pruneAndValidate ::
  (SymEvalConstr lang) =>
  PureSMT.SExpr ->
  Maybe PureSMT.SExpr ->
  [UniversalAxiom lang] ->
  SymEval lang PruneResult
pruneAndValidate cOut cIn axioms =
  SymEval $
    ReaderT $ \env ->
      StateT $ \st ->
        return (solvePropProblem (seeSolvers env) (CheckPropertyProblem cOut cIn axioms st (seeDefs env)), st)
