{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Pirouette.Term.Symbolic.Eval (
  -- * Runners
  -- ** General inputs and outputs
  AvailableFuel(..), Path(..), PathStatus(..), Constraint, SymVar,
  -- ** Base symbolic evaluation
  runFor, pathsFor,
  -- ** Incorrectness logic
  runIncorrectness, pathsIncorrectness, pathsIncorrectness_,
  UserDeclaredConstraints(..), UniversalAxiom(..), InCond(..), OutCond(..),
  EvaluationWitness(..),
  -- * Internal, used to build on top of 'SymEvalT'
  SymEvalConstr, SymEvalT, runSymEvalT
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader (ask)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Data hiding (eqT)
import Data.Foldable
import qualified Data.List as List
import qualified Data.Map.Strict as M
import ListT (ListT)
import qualified ListT
import Pirouette.Monad
import Pirouette.Monad.Maybe
import qualified Pirouette.SMT as SMT
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.Transformations
import Prettyprinter hiding (Pretty (..))

-- import Debug.Trace (trace)

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Show, Data, Typeable)

instance SMT.ToSMT SymVar where
  translate = SMT.translate . symVar

type Constraint lang = SMT.Constraint lang SymVar

symVarEq :: SymVar -> SymVar -> Constraint lang
symVarEq a b = SMT.And [SMT.VarEq (symVar a) (symVar b)]

(=:=) :: SymVar -> TermMeta lang SymVar -> Constraint lang
a =:= t = SMT.And [SMT.Assign (symVar a) t]

data PathStatus = Completed | OutOfFuel deriving (Eq, Show)

data Path lang res = Path
  { pathConstraint :: Constraint lang,
    pathGamma :: M.Map Name (Type lang),
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

deriving instance (Eq (Constraint lang), Eq (Type lang), Eq res) => Eq (Path lang res)
deriving instance (Show (Constraint lang), Show (Type lang), Show res) => Show (Path lang res)

data AvailableFuel = Fuel Int | InfiniteFuel
  deriving (Eq, Show)

fuelExhausted :: AvailableFuel -> Bool
fuelExhausted (Fuel n) = n <= 0
fuelExhausted InfiniteFuel = False

consumeOneUnitOfFuel :: AvailableFuel -> AvailableFuel
consumeOneUnitOfFuel (Fuel n) = Fuel (n - 1)
consumeOneUnitOfFuel i = i

instance Pretty AvailableFuel where
  pretty InfiniteFuel = "infinite"
  pretty (Fuel n) = pretty n

data SymEvalSt lang = SymEvalSt
  { sestConstraint :: Constraint lang,
    sestGamma :: M.Map Name (Type lang),
    sestFreshCounter :: Int,
    sestFuel :: AvailableFuel,
    -- | A branch that has been validated before is never validated again /unless/ we 'learn' something new.
    sestValidated :: Bool,
    sestKnownNames :: [Name] -- The list of names the SMT solver is aware of
  }

instance (LanguagePretty lang) => Pretty (SymEvalSt lang) where
  pretty SymEvalSt{..} =
    "Constraints are" <+> pretty sestConstraint <> "\n" <>
    "in environnement" <+> pretty (M.toList sestGamma) <> "\n" <>
    "with a counter at" <+> pretty sestFreshCounter <+>
    "and" <+> pretty sestFuel <+> "fuel remaining"

-- | Given a result and a resulting state, returns a 'Path' representing it.
path :: a -> SymEvalSt lang -> Path lang a
path x st =
  Path
    { pathConstraint = sestConstraint st,
      pathGamma = sestGamma st,
      pathStatus = if fuelExhausted (sestFuel st) then OutOfFuel else Completed,
      pathResult = x
    }

-- | A 'SymEvalT' is equivalent to a function with type:
--
-- > SymEvalSt lang -> SMT.Solver -> m [(a, SymEvalSt lang)]
newtype SymEvalT lang m a = SymEvalT {symEvalT :: StateT (SymEvalSt lang) (SMT.SolverT (ListT m)) a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadState (SymEvalSt lang))

type SymEvalConstr lang m = 
  (PirouetteDepOrder lang m, LanguagePretty lang, SMT.LanguageSMTBranches lang, MonadIO m)

symevalT :: (SymEvalConstr lang m) => AvailableFuel -> SymEvalT lang m a -> m [Path lang a]
symevalT initialFuel = runSymEvalT st0
  where
    st0 = SymEvalSt mempty M.empty 0 initialFuel False []

runSymEvalTRaw 
  :: (Monad m) => SymEvalSt lang -> SymEvalT lang m a
  -> SMT.SolverT (ListT m) (a, SymEvalSt lang)
runSymEvalTRaw st = flip runStateT st . symEvalT

-- | Running a symbolic execution will prepare the solver only once, then use a persistent session
--  to make all the necessary queries.
runSymEvalT :: (SymEvalConstr lang m) => SymEvalSt lang -> SymEvalT lang m a -> m [Path lang a]
runSymEvalT st symEvalT =
  ListT.toList $ do
    solvPair <- SMT.runSolverT s $ do
      usedNames <- prepSolver
      let newState = st {sestKnownNames = usedNames ++ sestKnownNames st}
      runSymEvalTRaw newState symEvalT
    let paths = uncurry path solvPair
    return paths
  where
    -- we'll rely on cvc4 with dbg messages
    s = SMT.cvc4_ALL_SUPPORTED False

    prepSolver :: (SymEvalConstr lang m) => SMT.SolverT (ListT m) [Name]
    prepSolver = do
      decls <- lift $ lift prtAllDefs
      dependencyOrder <- lift $ lift prtDependencyOrder
      declData <- runExceptT (SMT.declareDatatypes decls dependencyOrder)
      case declData of
        Right usedNames -> return usedNames
        Left e -> error e

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
prune :: forall lang m a. (Pretty a, SymEvalConstr lang m) => SymEvalT lang m a -> SymEvalT lang m a
prune xs = SymEvalT $
  StateT $ \st -> do
    (x, st') <- runSymEvalTRaw st xs
    -- trace ("  X is " ++ show (pretty x)) $ return ()
    -- trace ("  in the context " ++ show (pretty st')) $ return ()
    ok <- pathIsPlausible st'
    guard ok
    return (x, st')
  where
    pathIsPlausible :: (MonadIO n) => SymEvalSt lang -> SMT.SolverT n Bool
    pathIsPlausible env
      | sestValidated env = return True -- We already validated this branch before; nothing new was learnt.
      | otherwise = do
        SMT.solverPush
        decl <- runExceptT (SMT.declareVariables (sestGamma env))
        case decl of
          Right _ -> return ()
          Left s -> error s
        -- Here we do not care about the totality of the translation,
        -- since we want to prune unsatisfiable path.
        -- And if a partial translation is already unsat,
        -- so is the translation of the whole set of constraints.
        void $ SMT.assert (sestGamma env) (sestKnownNames env) (sestConstraint env)
        res <- SMT.checkSat
        SMT.solverPop
        return $ case res of
          SMT.Unsat -> False
          _ -> True

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

runEvaluation :: (SymEvalConstr lang m) => Term lang -> SymEvalT lang m (TermMeta lang SymVar)
runEvaluation t = do
  -- liftIO $ putStrLn $ "evaluating: " ++ show (pretty t)
  let (lams, _) = R.getHeadLams t
  svars <- declSymVars lams
  symeval (R.appN (termToMeta t) $ map (R.TermArg . (`R.App` []) . R.Meta) svars)

currentFuel :: (SymEvalConstr lang m) => SymEvalT lang m AvailableFuel
currentFuel = gets sestFuel

normalizeTerm :: (SymEvalConstr lang m) => TermMeta lang SymVar -> m (TermMeta lang SymVar)
normalizeTerm = destrNF >=> removeExcessiveDestArgs >=> constrDestrId

-- | Top level symbolic evaluation loop.
symeval :: (SymEvalConstr lang m)
        => TermMeta lang SymVar -> SymEvalT lang m (TermMeta lang SymVar)
symeval t = do
  fuelLeft <- currentFuel
  if fuelExhausted fuelLeft
    then pure t
    else do
      t' <- lift $ normalizeTerm t
      (tOneStepMore, somethingWasEvaluated) <- prune $ runWriterT (symEvalOneStep t')
      if somethingWasEvaluated == Any False
         then pure tOneStepMore
         else symeval tOneStepMore

-- | Take one step of evaluation.
-- We wrap everything in an additional 'Writer' which tells us
-- whether a step was taken at all.
symEvalOneStep 
  :: forall lang m. (SymEvalConstr lang m) 
  => TermMeta lang SymVar -> WriterT Any (SymEvalT lang m) (TermMeta lang SymVar)
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
    (evaluatedArgs, somethingWasEvaluated) <- listen $ mapM (R.argMapM return symEvalOneStep) args
    if somethingWasEvaluated == Any True
       then pure $ R.App hd evaluatedArgs
       else -- we could not evaluate arguments more,
            -- so go on and evaluate the built-in
         case SMT.branchesBuiltinTerm @lang builtin evaluatedArgs of
           Just branches -> asum $ flip map branches $ \(SMT.Branch additionalInfo newTerm) -> do
              lift $ learn additionalInfo
              consumeFuel
              pure newTerm
           _ -> pure $ R.App hd evaluatedArgs  -- no branching info.
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
        pure $ termToMeta body `R.appN` args
      -- If hd is a constructor, we symbolically evaluate the arguments and reconstruct the term
      -- by combining the paths with (>>>=), conjuncts all of the constraints. For instance,
      --
      -- > symeval (Cons x xs) ==
      -- >   let x'  = symeval x :: [(Constraint, X)]
      -- >       xs' = symeval xs :: [(Constraint, XS)]
      -- >    in [ (cx && cxs , Cons rx rxs)
      -- >       | (cx, rx) <- x' , (cxs, rxs) <- xs'
      -- >       , isSAT (cx && cxs) ]
      --
      Just (DConstructor _ _) -> justEvaluateArgs
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
      Just (DDestructor tyName) -> do
        Just (UnDestMeta _ _ tyParams term tyRes cases excess) <- lift $ lift $ runMaybeT (unDest t)
        Datatype _ _ _ consList <- lift $ lift $ prtTypeDefOf tyName
        -- We know what is the type of all the possible term results, its whatever
        -- type we're destructing applied to its arguments, making sure it contains
        -- no meta variables.
        let tyParams' = map typeFromMeta tyParams
        (term', somethingWasEvaluated) <- listen $ symEvalOneStep term
        -- We only do the case distinction if we haven't taken any step
        -- in the previous step. Otherwise it wouldn't be a "one step" evaluator.
        if somethingWasEvaluated == Any True
        then do let args' = R.TermArg term' : R.TyArg tyRes : map R.TermArg cases
                pure $ R.App hd (map R.TyArg tyParams ++ args' ++ excess)
        else asum $ -- traverse every possibility
          for2 consList cases $ \(consName, consTy) caseTerm -> do
            let instantiatedTy = subst (foldl' (\x y -> Just y :< x) (Inc 0) tyParams') consTy
            let (consArgs, _) = R.tyFunArgs instantiatedTy
            svars <- lift $ freshSymVars consArgs
            let symbArgs = map (R.TermArg . (`R.App` []) . R.Meta) svars
            let symbCons = R.App (R.Free $ TermSig consName) (map (R.TyArg . typeToMeta) tyParams' ++ symbArgs)
            let mconstr = unify term' symbCons
            case mconstr of
              Nothing -> empty
              Just constr -> do
                lift $ learn constr
                consumeFuel
                pure $ caseTerm `R.appN` symbArgs
          
  -- in any other case don't try too hard
  _ -> justEvaluateArgs
  where
    justEvaluateArgs = do
      evaluatedArgs <- mapM (R.argMapM return symEvalOneStep) args
      pure $ R.App hd evaluatedArgs

-- | Consume one unit of fuel.
-- This also tells the symbolic evaluator that a step was taken.
consumeFuel :: (SymEvalConstr lang m) => WriterT Any (SymEvalT lang m) ()
consumeFuel = do
  modify (\st -> st {sestFuel = consumeOneUnitOfFuel (sestFuel st)})
  tell (Any True)

-- | Required to run 'prune'
instance Pretty Any

unify :: (LanguageBuiltins lang) => TermMeta lang SymVar -> TermMeta lang SymVar -> Maybe (Constraint lang)
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

--- TMP CODE

instance (LanguagePretty lang, Pretty a) => Pretty (Path lang a) where
  pretty (Path conds gamma ps res) =
    vsep
      [ "With:" <+> pretty (M.toList gamma),
        "If:" <+> indent 2 (pretty conds),
        "Status:" <+> pretty ps,
        "Result:" <+> indent 2 (pretty res)
      ]

instance Pretty PathStatus where
  pretty Completed = "Completed"
  pretty OutOfFuel = "OutOfFuel"

instance Pretty SymVar where
  pretty (SymVar n) = pretty n

runFor :: (LanguagePretty lang, SymEvalConstr lang m, MonadIO m)
       => AvailableFuel -> Name -> Term lang -> m ()
runFor initialFuel nm t = do
  paths <- pathsFor initialFuel nm t
  mapM_ (liftIO . print . pretty) paths

pathsFor :: (LanguagePretty lang, SymEvalConstr lang m, MonadIO m)
         => AvailableFuel -> Name -> Term lang -> m [Path lang (TermMeta lang SymVar)]
pathsFor initialFuel _ t = symevalT initialFuel (runEvaluation t)

-- * All the functions related to symbolic execution guarded by user written predicates rather than fuel.

data UserDeclaredConstraints lang = UserDeclaredConstraints {
  udcInputs :: [(Name, Type lang)],
  udcOutputCond :: OutCond lang,
  udcInputCond :: InCond lang,
  udcAdditionalDefs :: IO [SimpleSMT.SExpr],
  udcAxioms :: [UniversalAxiom lang]
}

newtype OutCond lang = OutCond (TermMeta lang SymVar -> Constraint lang)
newtype InCond lang = InCond (Constraint lang)

data EvaluationWitness lang =
  Verified | CounterExample (TermMeta lang SymVar)
  deriving (Eq, Show)

data UniversalAxiom lang = UniversalAxiom {
  boundVars :: [(Name, Type lang)],
  axiomBody :: [SimpleSMT.SExpr] -> SimpleSMT.SExpr
}


runIncorrectness :: (SymEvalConstr lang  m, MonadIO m)
                 => UserDeclaredConstraints lang -> Term lang  -> m ()
runIncorrectness udc t = do
  paths <- pathsIncorrectness udc t
  if null paths
  then liftIO $ putStrLn "Condition VERIFIED"
  else mapM_ (liftIO . print . pretty) paths

pathsIncorrectness :: (SymEvalConstr lang  m, MonadIO m)
                   => UserDeclaredConstraints lang -> Term lang  -> m [Path lang (EvaluationWitness lang)]
pathsIncorrectness udc t = symevalT InfiniteFuel $ pathsIncorrectnessWorker udc t

pathsIncorrectness_ :: (SymEvalConstr lang  m, MonadIO m)
                    => (SimpleSMT.Solver -> m (UserDeclaredConstraints lang)) -> Term lang
                    -> m [Path lang (EvaluationWitness lang)]
pathsIncorrectness_ getUdc t = symevalT InfiniteFuel $ do
  solver <- SymEvalT $ lift $ SMT.SolverT ask
  udc <- lift $ getUdc solver
  pathsIncorrectnessWorker udc t

pathsIncorrectnessWorker :: (SymEvalConstr lang  m, MonadIO m)
                         => UserDeclaredConstraints lang -> Term lang  -> SymEvalT lang m (EvaluationWitness lang)
pathsIncorrectnessWorker UserDeclaredConstraints {..} t = do
    void $ liftIO udcAdditionalDefs
    svars <- declSymVars udcInputs
    let tApplied = R.appN (termToMeta t) $ map (R.TermArg . (`R.App` []) . R.Meta) svars
    liftIO $ putStrLn $ "Conditionally evaluating: " ++ show (pretty tApplied)
    conditionalEval tApplied udcOutputCond udcInputCond udcAxioms

conditionalEval :: (SymEvalConstr lang m, MonadIO m)
                => TermMeta lang SymVar -> OutCond lang -> InCond lang -> [UniversalAxiom lang]
                -> SymEvalT lang m (EvaluationWitness lang)
conditionalEval t (OutCond q) (InCond p) axioms = do
  normalizedT <- lift $ normalizeTerm t
  (t', somethingWasDone) <- runWriterT (symEvalOneStep normalizedT)
  liftIO $ putStrLn $ "normalized: " ++ show (pretty t')
  result <- pruneAndValidate (q t') p axioms
  liftIO $ putStrLn $ "result? " ++ show result
  case result of
    SMT.Unsat -> pure Verified
    SMT.Sat -> pure (CounterExample t)
    _ -> if somethingWasDone == Any False
            then pure (CounterExample t) -- cannot check more
            else conditionalEval t' (OutCond q) (InCond p) axioms    

-- | Prune the set of paths in the current set.
pruneAndValidate :: (SymEvalConstr lang m) => Constraint lang -> Constraint lang -> [UniversalAxiom lang] -> SymEvalT lang m SimpleSMT.Result
pruneAndValidate cOut cIn axioms =
  SymEvalT $ StateT $ \st -> do
    contradictProperty <- checkProperty cOut cIn axioms st
    liftIO $ putStrLn $ show (pretty cOut) ++ " => " ++ show (pretty cIn) ++ "? " ++ show contradictProperty
    return (contradictProperty, st)

instantiateAxiomWithVars :: (SMT.LanguageSMT lang, MonadIO m) => [UniversalAxiom lang] -> SymEvalSt lang -> SMT.SolverT m ()
instantiateAxiomWithVars axioms env =
  SMT.SolverT $ do
    solver <- ask
    liftIO $
      mapM_
        (\(name, ty) ->
          mapM_
            (\UniversalAxiom{..} ->
              when (List.any (\(_,tyV) -> tyV == ty) boundVars) $
                if length boundVars == 1
                then
                  void $ SimpleSMT.assert solver (axiomBody [SimpleSMT.symbol (SMT.toSmtName name)])
                else error "Several universally bound variables not handled yet" -- TODO
            )
            axioms
        )
        (M.toList $ sestGamma env)

-- Our aim is to prove that
-- (pathConstraints /\ cOut) => cIn.
-- This is equivalent to the unsatisfiability of
-- pathConstraints /\ cOut /\ (not cIn).
checkProperty :: (SMT.LanguageSMT lang, MonadIO m) => Constraint lang -> Constraint lang -> [UniversalAxiom lang] -> SymEvalSt lang -> SMT.SolverT m SMT.Result
checkProperty cOut cIn axioms env = do
  SMT.solverPush
  let vars = sestGamma env
  decl <- runExceptT (SMT.declareVariables vars)
  instantiateAxiomWithVars axioms env
  case decl of
    Right _ -> return ()
    Left s -> error s
  cstrTotal <- SMT.assert vars (sestKnownNames env) (sestConstraint env)
  outTotal <- SMT.assert vars (sestKnownNames env) cOut
  inTotal <- SMT.assertNot vars (sestKnownNames env) cIn
  result <- SMT.checkSat
  SMT.solverPop
  case result of
    SMT.Sat ->
      if cstrTotal && outTotal && inTotal
      then return SMT.Sat
      -- If a partial translation of the constraints is SAT,
      -- it does not guarantee us that the full set of constraints is satisfiable.
      else return SMT.Unknown
    _ -> return result

instance LanguagePretty lang => Pretty (EvaluationWitness lang) where
  pretty Verified = "Verified"
  pretty (CounterExample t) = "COUNTER-EXAMPLE: The result is\n" <> pretty t
