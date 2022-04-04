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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}

module Pirouette.Term.Symbolic.Eval where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader (ask)
import Control.Monad.Except
import Control.Monad.State
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

import Debug.Trace (trace)

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Show, Data, Typeable)

instance SMT.ToSMT SymVar where
  translate = SMT.translate . symVar

type Constraint lang = SMT.Constraint lang SymVar

symVarEq :: SymVar -> SymVar -> Constraint lang
symVarEq a b = SMT.And [SMT.VarEq (symVar a) (symVar b)]

(=:=) :: SymVar -> TermMeta lang SymVar -> Constraint lang
a =:= t = SMT.And [SMT.Assign (symVar a) t]

data PathStatus = Completed | OutOfFuel

data Path lang res = Path
  { pathConstraint :: Constraint lang,
    pathGamma :: M.Map Name (Type lang),
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

data SymEvalSt lang = SymEvalSt
  { sestConstraint :: Constraint lang,
    sestGamma :: M.Map Name (Type lang),
    sestFreshCounter :: Int,
    sestFuel :: Int,
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
      pathStatus = if sestFuel st <= 0 then OutOfFuel else Completed,
      pathResult = x
    }

-- | A 'SymEvalT' is equivalent to a function with type:
--
-- > SymEvalSt lang -> SMT.Solver -> m [(a, SymEvalSt lang)]
newtype SymEvalT lang m a = SymEvalT {symEvalT :: StateT (SymEvalSt lang) (SMT.SolverT (ListT m)) a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadState (SymEvalSt lang))

type SymEvalConstr lang m = (PirouetteDepOrder lang m, LanguagePretty lang, SMT.LanguageSMT lang, MonadIO m)

symevalT :: (SymEvalConstr lang m) => SymEvalT lang m a -> m [Path lang a]
symevalT = runSymEvalT st0
  where
    st0 = SymEvalSt mempty M.empty 0 10 False []

runSymEvalTRaw :: (Monad m) => SymEvalSt lang -> SymEvalT lang m a -> SMT.SolverT (ListT m) (a, SymEvalSt lang)
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
        Left s -> error s

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
    trace ("  X is " ++ show (pretty x)) $ return ()
    trace ("  in the context " ++ show (pretty st')) $ return ()
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

freshSymVar :: (SymEvalConstr lang m) => Type lang -> SymEvalT lang m SymVar
freshSymVar ty = head <$> freshSymVars [ty]

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
  liftIO $ putStrLn $ "evaluating: " ++ show (pretty t)
  let (lams, _) = R.getHeadLams t
  svars <- declSymVars lams
  symeval (R.appN (termToMeta t) $ map (R.TermArg . (`R.App` []) . R.Meta) svars)

consumeGas :: (SymEvalConstr lang m) => SymEvalT lang m a -> SymEvalT lang m a
consumeGas f = modify (\st -> st {sestFuel = sestFuel st - 1}) >> f

currentGas :: (SymEvalConstr lang m) => SymEvalT lang m Int
currentGas = gets sestFuel

normalizeTerm :: (SymEvalConstr lang m) => TermMeta lang SymVar -> m (TermMeta lang SymVar)
normalizeTerm = destrNF >=> removeExcessiveDestArgs >=> constrDestrId

symeval :: (SymEvalConstr lang m) => TermMeta lang SymVar -> SymEvalT lang m (TermMeta lang SymVar)
symeval t = do
  t' <- lift $ normalizeTerm t
  fuelLeft <- currentGas
  if fuelLeft <= 0
    then return t'
    else prune $ symeval' t'

prtMaybeDefOf :: (PirouetteReadDefs lang m) => VarMeta lang meta -> m (Maybe (Definition lang))
prtMaybeDefOf (R.Free (TermSig n)) = Just <$> prtDefOf n
prtMaybeDefOf _ = pure Nothing

symeval' :: (SymEvalConstr lang m) => TermMeta lang SymVar -> SymEvalT lang m (TermMeta lang SymVar)
-- We cannot symbolic-evaluate polymorphic terms
symeval' R.Abs {} = error "Can't symbolically evaluate polymorphic things"
-- If we're forced to symbolic evaluate a lambda, we create a new metavariable
-- and evaluate the corresponding application.
symeval' t@(R.Lam (R.Ann x) ty _) = do
  let ty' = typeFromMeta ty
  [svars] <- declSymVars [(x, ty')]
  symeval' $ t `R.app` R.TermArg (R.App (R.Meta svars) [])
-- If we're evaluating an applcation, we distinguish between a number
-- of constituent cases:
symeval' t@(R.App hd args) = do
  mDefHead <- lift $ prtMaybeDefOf hd
  case mDefHead of
    Nothing -> return t
    Just def -> case def of
      DTypeDef _ -> error "Can't evaluate typedefs"
      -- If hd is a defined function, we inline its definition and symbolically evaluate
      -- the result consuming one gas.
      DFunction _rec body _ ->
        consumeGas . symeval $ termToMeta body `R.appN` args
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
      DConstructor _ _18' -> R.App hd <$> mapM (R.argMapM return symeval) args
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
      DDestructor tyName -> do
        Just (UnDestMeta _ _ tyParams term _ cases _) <- lift $ runMaybeT (unDest t)
        Datatype _ _ _ consList <- lift $ prtTypeDefOf tyName
        -- We know what is the type of all the possible term results, its whatever
        -- type we're destructing applied to its arguments, making sure it contains
        -- no meta variables.
        let tyParams' = map typeFromMeta tyParams
        term' <- symeval term
        asum $
          for2 consList cases $ \(consName, consTy) caseTerm -> do
            let instantiatedTy = subst (foldl' (\s t -> Just t :< s) (Inc 0) tyParams') consTy
            let (consArgs, _) = R.tyFunArgs instantiatedTy
            svars <- freshSymVars consArgs
            let symbArgs = map (R.TermArg . (`R.App` []) . R.Meta) svars
            let symbCons = R.App (R.Free $ TermSig consName) (map (R.TyArg . typeToMeta) tyParams' ++ symbArgs)
            let mconstr = unify term' symbCons
            case mconstr of
              Nothing -> empty
              Just constr -> learn constr >> consumeGas (symeval $ caseTerm `R.appN` symbArgs)

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

runFor :: (LanguagePretty lang, SymEvalConstr lang m, MonadIO m) => Name -> Term lang -> m ()
runFor _ t = do
  paths <- symevalT (runEvaluation t)
  mapM_ (liftIO . print . pretty) paths

-- * All the functions related to symbolic execution guarded by user written predicates rather than fuel.

newtype OutCond lang = OutCond (TermMeta lang SymVar -> Constraint lang)
newtype InCond lang = InCond (Constraint lang)

data EvaluationWitness lang =
  Verified | CounterExample (TermMeta lang SymVar)

data UniversalAxiom lang = UniversalAxiom {
  boundVars :: [(Name, Type lang)],
  axiomBody :: [SimpleSMT.SExpr] -> SimpleSMT.SExpr
}

conditionalEval :: (SymEvalConstr lang m, MonadIO m) => TermMeta lang SymVar -> OutCond lang -> InCond lang -> [UniversalAxiom lang]-> SymEvalT lang m (EvaluationWitness lang)
conditionalEval t (OutCond q) (InCond p) axioms = do
  toEvaluateMore <- pruneAndValidate (q t) p axioms
  if toEvaluateMore
  then do
    t' <- symEvalOneStep t
    conditionalEval t' (OutCond q) (InCond p) axioms
  else
    return (CounterExample t)

symEvalOneStep :: (SymEvalConstr lang m) => TermMeta lang SymVar -> SymEvalT lang m (TermMeta lang SymVar)
-- We cannot symbolic-evaluate polymorphic terms
symEvalOneStep R.Abs {} = error "Can't symbolically evaluate polymorphic things"
-- If we're forced to symbolic evaluate a lambda, we create a new metavariable
-- and evaluate the corresponding application.
symEvalOneStep t@(R.Lam (R.Ann x) ty _) = do
  let ty' = typeFromMeta ty
  [svars] <- declSymVars [(x, ty')]
  R.Lam (R.Ann x) ty <$> symEvalOneStep (t `R.app` R.TermArg (R.App (R.Meta svars) []))
-- If we're evaluating an applcation, we distinguish between a number
-- of constituent cases:
symEvalOneStep t@(R.App hd args) = do
  mDefHead <- lift $ prtMaybeDefOf hd
  case mDefHead of
    -- If hd is not defined, we symbolically evaluate the arguments and reconstruct the term.
    Nothing -> do
      evaluatedArgs <- mapM (R.argMapM return symEvalOneStep) args
      return $ R.App hd evaluatedArgs
    Just def -> case def of
      DTypeDef _ -> error "Can't evaluate typedefs"
      -- If hd is a defined function, we inline its definition.
      DFunction _rec body _ ->
        return $ termToMeta body `R.appN` args
      -- If hd is a constructor, we symbolically evaluate the arguments and reconstruct the term.
      DConstructor _ _ -> do
        evaluatedArgs <- mapM (R.argMapM return symEvalOneStep) args
        return $ R.App hd evaluatedArgs
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
      DDestructor tyName -> do
        Just (UnDestMeta _ _ tyParams term tyRes cases excess) <- lift $ runMaybeT (unDest t)
        Datatype _ _ _ consList <- lift $ prtTypeDefOf tyName
        -- We know what is the type of all the possible term results, its whatever
        -- type we're destructing applied to its arguments, making sure it contains
        -- no meta variables.
        let tyParams' = map typeFromMeta tyParams
        term' <- symEvalOneStep term
        if term == term'
        then
          asum $
            for2 consList cases $ \(consName, consTy) caseTerm -> do
              let instantiatedTy = subst (foldl' (\s t -> Just t :< s) (Inc 0) tyParams') consTy
              let (consArgs, _) = R.tyFunArgs instantiatedTy
              svars <- freshSymVars consArgs
              let symbArgs = map (R.TermArg . (`R.App` []) . R.Meta) svars
              let symbCons = R.App (R.Free $ TermSig consName) (map (R.TyArg . typeToMeta) tyParams' ++ symbArgs)
              let mconstr = unify term' symbCons
              case mconstr of
                Nothing -> empty
                Just constr -> do
                  learn constr
                  return (caseTerm `R.appN` symbArgs)
        else
          return $ R.App hd (map R.TyArg tyParams ++ R.TermArg term' : R.TyArg tyRes : map R.TermArg cases ++ excess)

-- | Prune the set of paths in the current set.
pruneAndValidate :: (SymEvalConstr lang m) => Constraint lang -> Constraint lang -> [UniversalAxiom lang] -> SymEvalT lang m Bool
pruneAndValidate cOut cIn axioms =
  SymEvalT $ StateT $ \st -> do
    contradictProperty <- checkProperty cOut cIn axioms st
    case contradictProperty of
      SMT.Unsat -> empty
      SMT.Sat -> return (False, st)
      SMT.Unknown -> return (True, st)

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
