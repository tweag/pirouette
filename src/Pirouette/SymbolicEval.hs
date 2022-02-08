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

module Pirouette.SymbolicEval where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Data hiding (eqT)
import Data.Foldable
import Data.Functor
import Data.List (foldl', intersperse)
import qualified Data.Map as Map
import qualified Data.Map.Strict as M
import Prettyprinter hiding (Pretty (..))
import Data.Void (absurd)
import ListT (ListT)
import qualified ListT
import Pirouette.Monad
import Pirouette.Monad.Maybe
import Pirouette.PlutusIR.Utils
import Pirouette.SMT (smtCheckPathConstraint)
import qualified Pirouette.SMT.SimpleSMT as SmtLib (Result (..))
import Pirouette.Term.FromPlutusIR (PirTerm, PirType, PlutusIR)
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.Transformations

data Constraint lang
  = SymVar :== PrtTermMeta lang SymVar
  | And [Constraint lang]
  | Bot

instance Semigroup (Constraint lang) where
  (<>) = andConstr

instance Monoid (Constraint lang) where
  mempty = And []

-- Essentially list concatenation, with the specificity that `Bot` is absorbing.
andConstr :: Constraint lang -> Constraint lang -> Constraint lang
andConstr Bot _ = Bot
andConstr _ Bot = Bot
andConstr (And l) (And m) = And (l ++ m)
andConstr (And l) y = And (y : l)
andConstr x (And m) = And (x : m)
andConstr x y = And [x, y]

data Path lang res = Path
  { pathConstraint :: Constraint lang,
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

data PathStatus = Pruned | Ongoing

instance Semigroup PathStatus where
  Pruned <> _ = Pruned
  _ <> Pruned = Pruned
  _ <> _ = Ongoing

instance Applicative (Path lang) where
  pure = Path mempty Ongoing
  f <*> x =
    Path
      (pathConstraint f <> pathConstraint x)
      (pathStatus f <> pathStatus x)
      (pathResult f (pathResult x))

data SymEvalEnv lang = SymEvalEnv
  { seeFuel :: Integer,
    seeConstraint :: Constraint lang
  }

seeAndConstrs :: Constraint lang -> SymEvalEnv lang -> SymEvalEnv lang
seeAndConstrs c (SymEvalEnv fuel cs) = SymEvalEnv fuel (c <> cs)

data SymEvalSt lang = SymEvalSt
  { sestEnv :: M.Map Name (PrtType lang)
  , sestFreshCounter :: Int
  }

newtype SymEvalT lang m a = SymEvalT {symEvalT :: ReaderT (SymEvalEnv lang) (StateT (SymEvalSt lang) (ListT m)) (Path lang a)}
  deriving (Functor)

runSymEvalT' :: (Monad m) => SymEvalEnv lang -> SymEvalSt lang -> SymEvalT lang m a -> ListT m (Path lang a, SymEvalSt lang)
runSymEvalT' e st = flip runStateT st . flip runReaderT e . symEvalT

runSymEvalT :: (Monad m) => SymEvalEnv lang -> SymEvalSt lang -> SymEvalT lang m a -> m [(Path lang a, SymEvalSt lang)]
runSymEvalT e st = ListT.toList . runSymEvalT' e st

symevalT :: (Monad m) => SymEvalT lang m a -> m [Path lang a]
symevalT = fmap (map fst) . runSymEvalT e0 st0
  where
    e0 = SymEvalEnv 10 mempty
    st0 = SymEvalSt M.empty 0

instance (Monad m) => Applicative (SymEvalT lang m) where
  -- TODO: should we get the constraints from the env and put them on the path?
  pure x = SymEvalT $ ReaderT $ \e -> StateT $ \st -> ListT.fromFoldable [(Path (seeConstraint e) Ongoing x, st)]
  (<*>) = ap

instance (Monad m) => Monad (SymEvalT lang m) where
  xs >>= f = SymEvalT $
    ReaderT $ \e -> StateT $ \st -> do
      (x, st') <- runSymEvalT' e st xs
      (y, st'') <- runSymEvalT' (seeAndConstrs (pathConstraint x) e) st' (f $ pathResult x)
      return (y, st'')

instance (Monad m) => Alternative (SymEvalT lang m) where
  empty = SymEvalT $ ReaderT $ \_ -> StateT $ const empty

  xs <|> ys = SymEvalT $
    ReaderT $ \e -> StateT $ \st ->
      runSymEvalT' e st xs <|> runSymEvalT' e st ys

instance (Monad m) => MonadState (SymEvalSt lang) (SymEvalT lang m) where
  state f = SymEvalT $ ReaderT $ \_ -> state (first pure . f)

instance (Monad m) => MonadReader (SymEvalEnv lang) (SymEvalT lang m) where
  ask = SymEvalT $ ReaderT $ \e -> return (pure e)
  local f = SymEvalT . local f . symEvalT

instance MonadTrans (SymEvalT lang) where
  lift x = SymEvalT $ lift $ lift $ lift $ fmap pure x

instance (MonadFail m) => MonadFail (SymEvalT lang m) where
  fail = lift . fail

type SymEvalConstr lang m = (PirouetteDepOrder lang m, PrettyLang lang, MonadIO m)

instance (MonadIO m) => MonadIO (SymEvalT lang m) where
  liftIO = lift . liftIO

prune :: (SymEvalConstr lang m) => SymEvalT lang m a -> SymEvalT lang m a
prune xs = SymEvalT $
  ReaderT $ \e -> StateT $ \st -> do
    (x, st') <- runSymEvalT' e st xs
    ok <- lift $ pathIsPlausible x (sestEnv st')
    guard ok
    return (x, st')
  where
    pathIsPlausible :: (Monad m) => Path lang a -> M.Map name (PrtType lang) -> m Bool
    pathIsPlausible p env = return True -- TODO: send path constraint to SMT?

learn :: (SymEvalConstr lang m) => Constraint lang -> SymEvalT lang m a -> SymEvalT lang m a
learn c f = do
  cs <- asks seeConstraint
  liftIO $ do
    putStrLn ("I knew: " ++ show (pretty cs))
    putStrLn ("I'm learning: " ++ show (pretty c))
  r <- local (seeAndConstrs c) f
  liftIO $ putStrLn "Forgotten"
  return r

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Show, Data, Typeable)

runEvaluation :: (SymEvalConstr lang m) => Term lang Name -> SymEvalT lang m (TermMeta lang SymVar Name)
runEvaluation t = do
  let (lams, body) = R.getHeadLams t
  withSymVars lams $ \svars ->
    symeval (R.appN (prtTermToMeta body) $ map (R.Arg . (`R.App` []) . R.M) svars)

withSymVars :: (SymEvalConstr lang m) => [(Name, PrtType lang)] -> ([SymVar] -> SymEvalT lang m a) -> SymEvalT lang m a
withSymVars vs f = do
  old <- get
  modify (\st -> st { sestEnv = M.union (sestEnv st) (M.fromList vs) })
  f (map (SymVar . fst) vs) <* put old

withFreshSymVar :: (SymEvalConstr lang m) => PrtType lang -> (SymVar -> SymEvalT lang m a) -> SymEvalT lang m a
withFreshSymVar ty f = withFreshSymVars [ty] (\[x] -> f x)

withFreshSymVars :: (SymEvalConstr lang m) => [PrtType lang] -> ([SymVar] -> SymEvalT lang m a) -> SymEvalT lang m a
withFreshSymVars [] f = f []
withFreshSymVars tys f = do
  let n = length tys
  ctr <- gets sestFreshCounter
  modify (\st -> st { sestFreshCounter = sestFreshCounter st + n })
  let vars = zipWith (\i ty -> (Name "s" (Just i) , ty)) [ctr..] tys
  withSymVars vars f

consumeGas :: (SymEvalConstr lang m) => SymEvalT lang m a -> SymEvalT lang m a
consumeGas = local (\e -> e { seeFuel = seeFuel e - 1 })

normalizeTerm :: (SymEvalConstr lang m) => TermMeta lang SymVar Name -> m (TermMeta lang SymVar Name)
normalizeTerm = destrNF >=> removeExcessiveDestArgs >=> constrDestrId

singlePathStatus :: (Monad m) => PathStatus -> a -> SymEvalT lang m a
singlePathStatus ps res =
  SymEvalT $ ReaderT $ \e -> StateT $ \st -> ListT.fromFoldable [(Path (seeConstraint e) ps res, st)]

outOfFuel :: (Monad m) => a -> SymEvalT lang m a
outOfFuel = singlePathStatus Pruned

completed :: (Monad m) => a -> SymEvalT lang m a
completed = singlePathStatus Ongoing

symeval :: (SymEvalConstr lang m) => TermMeta lang SymVar Name -> SymEvalT lang m (TermMeta lang SymVar Name)
symeval t = do
  t' <- lift $ normalizeTerm t
  fuelLeft <- asks seeFuel
  if fuelLeft <= 0
    then outOfFuel t'
    else prune $ symeval' t'

prtMaybeDefOf :: (PirouetteReadDefs lang m) => PrtVarMeta lang meta -> m (Maybe (PrtDef lang))
prtMaybeDefOf (R.F (FreeName n)) = Just <$> prtDefOf n
prtMaybeDefOf _ = pure Nothing

symeval' :: (SymEvalConstr lang m) => TermMeta lang SymVar Name -> SymEvalT lang m (TermMeta lang SymVar Name)
-- We cannot symbolic-evaluate polymorphic terms
symeval' R.Abs {} = error "Can't symbolically evaluate polymorphic things"
-- If we're forced to symbolic evaluate a lambda, we create a new metavariable
-- and evaluate the corresponding application.
symeval' t@(R.Lam (R.Ann x) ty body) = do
  let ty' = prtTypeFromMeta ty
  withSymVars [(x, ty')] $ \[svars] ->
    symeval' $ t `R.app` R.Arg (R.App (R.M svars) [])
-- If we're evaluating an applcation, we distinguish between a number
-- of constituent cases:
symeval' t@(R.App hd args) = do
  mDefHead <- lift $ prtMaybeDefOf hd
  case mDefHead of
    Nothing -> completed t
    Just def -> case def of
      DTypeDef _ -> error "Can't evaluate typedefs"
      -- If hd is a defined function, we inline its definition and symbolically evaluate
      -- the result consuming one gas.
      DFunction _rec body ty ->
        consumeGas . symeval $ prtTermToMeta body `R.appN` args
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
      DConstructor ix tyName -> R.App hd <$> mapM (R.argMapM return symeval) args
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
        Just (UnDestMeta _ _ tyParams term _ cases excess) <- lift $ runMaybeT (unDest t)
        Datatype _ _ _ consList <- lift $ prtTypeDefOf tyName
        -- We know what is the type of all the possible term results, its whatever
        -- type we're destructing applied to its arguments, making sure it contains
        -- no meta variables.
        let tyParams' = map prtTypeFromMeta tyParams
        let ty = R.TyApp (R.F $ TyFree tyName) tyParams'
        term' <- symeval term
        withFreshSymVar ty $ \svar -> do
          learn (svar :== term') $
            asum (zipWith (symevalAssuming tyParams' svar) consList cases)

symevalAssuming ::
  (SymEvalConstr lang m) =>
  [PrtType lang] ->
  SymVar ->
  (Name, PrtType lang) ->
  PrtTermMeta lang SymVar ->
  SymEvalT lang m (PrtTermMeta lang SymVar)
symevalAssuming tyParams svar (consName, consTy) term = prune $ do
  let (args, res) = R.tyFunArgs consTy
  withFreshSymVars args $ \svars -> do
    let symbCons =
          R.App (R.F $ FreeName consName) $
            map (R.TyArg . prtTypeToMeta) tyParams ++ map (R.Arg . (`R.App` []) . R.M) svars
    learn (svar :== symbCons) $ consumeGas $ symeval term

--- TMP CODE

instance (PrettyLang lang, Pretty a) => Pretty (Path lang a) where
  pretty (Path conds Ongoing res) =
    "If:\n" <> indent 2 (pretty conds)
      <> "\nthe output is:\n"
      <> indent 2 (pretty res)
  pretty (Path conds Pruned res) =
    "If:\n" <> indent 2 (pretty conds)
      <> "\nthe computation got stuck on:\n"
      <> indent 2 (pretty res)

instance Pretty SymVar where
  pretty (SymVar n) = pretty n

instance (PrettyLang lang) => Pretty (Constraint lang) where
  pretty (n :== term) =
    pretty n <+> "↦" <+> pretty term
  pretty Bot =
    "⊥"
  pretty (And []) =
    "⊤"
  pretty (And l) =
    mconcat $ intersperse "\n∧ " (map pretty l)

runFor :: (PrettyLang lang, SymEvalConstr lang m , MonadIO m) => Name -> PrtTerm lang -> m ()
runFor n t = do
  paths <- symevalT (runEvaluation t)
  mapM_ (liftIO . print . pretty) paths


--- OLD CODE


{-
        withConsumedGas (symeval term)
          >>>>= \term' -> withFreshSymVar ty $ \svar -> do
            forT consList $ \(cons, _) -> _
-}

{-
forT :: (Monad m , Alternative f) => [a] -> (a -> m (f b)) -> m (f b)
forT as f = asum <$> mapM f as

infixl 1 >>>=

(>>>=) ::
  (MonadSymEval lang m, Alternative t, Traversable t) =>
  m (t (Path a)) ->
  (a -> m b) ->
  m (t (Path b))
x >>>= f = x >>= mapM (`combine` f) -- TODO: prune paths?

(>>>>=) ::
  (MonadSymEval lang m, Alternative t, Traversable t) =>
  m (t (Path a)) ->
  (a -> m (t b)) ->
  m (t (Path b))
x >>>>= f = x >>= fmap pathJoin . mapM (`combine` f)
  where
    pathJoin :: (Applicative t, Traversable t) => t (Path (t a)) -> t (Path a)
    pathJoin = join . fmap sequenceA

-- TODO: Maybe we shouldn't have (t (Path TermMeta)), but define
-- a "Paths" monad and this combination of paths we just wrote here
-- should be the bind: I'd like to make it explicit that we're building
-- a tree of paths
combine :: (MonadSymEval lang m) => Path a -> (a -> m b) -> m (Path b)
combine p f =
  asks (Path . (pathConstraint p <>) . seeConstraint)
    <*> pure (pathStatus p)
    <*> f (pathResult p)

freeName :: Name -> PrtTermMeta lang meta
freeName = (`R.App` []) . R.F . FreeName

distr :: (Alternative t) => [R.Arg a (t (Path b))] -> t (Path [R.Arg a b])
distr = fmap (traverse distrArg) . traverse distrArg
  where
    distrArg :: (Applicative t) => R.Arg a (t b) -> t (R.Arg a b)
    distrArg (R.TyArg a) = pure (R.TyArg a)
    distrArg (R.Arg tb) = fmap R.Arg tb

-- getPathConstraintIfSAT :: (MonadSymEval lang m) => m Constraint
-- getPathConstraintIfSAT = do
--   constr <- asks seeConstraint
--   env <- asks seeEnv
--   plausibleBranch <- sendToSMT constr env
--   guard plausibleBranch
--   return constr

sendToSMT :: (MonadSymEval lang m) => Constraint -> M.Map Name (PrtType lang) -> m Bool
sendToSMT Bot _ = return False
sendToSMT (And []) _ = return True
sendToSMT constr env = return True

-}

-- sendToSMT constr env =
--   do
--     smtResult <- smtCheckPathConstraint (Map.fromList env) constr
--     return $
--       case smtResult of
--         SmtLib.Unsat -> False
--         _ -> True

{-

-- The result of symbolically executing `f arg1 arg2 arg3`
-- is a list of branches.
data SymbRes = SymbRes Name [Name] [CstrBranch]

instance Pretty SymbRes where
  pretty (SymbRes f args cstr) =
    "When evaluating" <+> pretty f
      <+> mconcat (intersperse " " (map pretty args))
      <> "\n"
      <> pretty cstr

-- The fuel datatype represents the reason why the computation of a branch ended.
data Fuel = OutOfFuel | NaturalEnd

-- It is a disjunction to know is fuel went over in one of the branch.
fuelOver :: Fuel -> Fuel -> Fuel
fuelOver OutOfFuel _ = OutOfFuel
fuelOver NaturalEnd x = x

-- A branch of the symbolic execution is a result term and
-- the constraint to fulfill to reach this branch.
-- Each branch also contains an indication of the reason leading to the generation of this branch,
-- either this path is fully evaluated, or the evaluation was interupted due to lack of fuel.
data CstrBranch = CstrBranch Fuel PirTerm Constraint

instance Pretty CstrBranch where
  pretty (CstrBranch NaturalEnd t conds) =
    "If:\n" <> indent 2 (pretty conds)
      <> "\nthe output is:\n"
      <> indent 2 (pretty t)
  pretty (CstrBranch OutOfFuel t conds) =
    "If:\n" <> indent 2 (pretty conds)
      <> "\nthe computation got stuck on:\n"
      <> indent 2 (pretty t)

true :: Constraint
true = And []

-- The main function. It takes a function name and its definition and output a result of symbolic execution.
-- Since we are doing inlining, we access symbol definition,
-- so this output is in a `PirouetteReadDefs` monad.
-- Since we are using the SMT solver, which requires types to be declared
-- to respect the dependency order, we even use `PirouetteDepOrder`.
evaluate :: (PirouetteDepOrder PlutusIR m, MonadIO m) => Name -> PirTerm -> m SymbRes
evaluate = auxEvaluateInputs []
  where
    -- We try to inline everything
    -- We do at most `fuel` inlining. After it, the symbolic evaluation of `t` simply output
    -- `CstrBranch t true`.
    mainFuel :: Int
    mainFuel = 10

    -- The first step is to collect the arguments of the function in a list of name.
    auxEvaluateInputs ::
      (PirouetteDepOrder PlutusIR m, MonadIO m) =>
      [(Name, PirType)] ->
      Name ->
      PirTerm ->
      m SymbRes
    auxEvaluateInputs vars mainFun t@(R.App _ _) =
      SymbRes mainFun (map fst vars) <$> evalStateT (auxEvaluate mainFuel true t) vars
    auxEvaluateInputs vars mainFun (R.Lam a ty t) =
      auxEvaluateInputs ((R.ann a, ty) : vars) mainFun t
    auxEvaluateInputs vars mainFun (R.Abs a _ t) =
      auxEvaluateInputs vars mainFun t

    -- Once all the names of the argument variables have been collected, we start the symbolic execution part.
    -- This is in a `State` monad, since the fuel for inlining and the names of already met variables should be shared between the symbolic evaluation of the different arguments of a function.
    auxEvaluate ::
      (PirouetteDepOrder PlutusIR m, MonadIO m) =>
      Int ->
      Constraint ->
      PirTerm ->
      StateT [(Name, PirType)] m [CstrBranch]
    auxEvaluate _ Bot _ = return []
    auxEvaluate remainingFuel conds t@(R.App hd args) = do
      vars <- get
      if remainingFuel == 0
        then -- If fuel is over, then we simply output the term as is.
          return [CstrBranch OutOfFuel t conds]
        else case hd of
          -- TODO: In all those cases, is it interesting to symbolically evaluate the arguments?
          R.M _ -> error "imp: we're using no meta variables (yet!)"
          R.B (R.Ann _) _ -> return [CstrBranch NaturalEnd t conds]
          R.F (Constant _) -> return [CstrBranch NaturalEnd t conds]
          R.F (Builtin _) -> return [CstrBranch NaturalEnd t conds]
          R.F Bottom -> return [CstrBranch NaturalEnd t conds]
          -- Here is the interesting case, we are symbolically executing an application of a symbol which is in the `PirouetteReadDefs` monad.
          R.F (FreeName f) -> do
            def <- prtDefOf f
            case def of
              -- If we are dealing with a defined symbol,
              -- we simply have to inline its definition.
              DFunction _ u _ -> do
                -- It is the inlinings which consume the fuel.
                auxEvaluate (remainingFuel - 1) conds
                  =<< normalizeTerm
                    ( R.appN
                        (deshadowBoundNamesWithForbiddenNames (map fst vars) u)
                        args
                    )
              -- If the studied term is headed by a constructor, we have to symbolically execute the arguments,
              -- but not the head.
              DConstructor {} ->
                case args of
                  -- If there are no arguments, it is over.
                  [] -> return [CstrBranch NaturalEnd (R.appN (signatureSymbol f) []) conds]
                  _ -> do
                    -- Else we symbolically execute the arguments.
                    resArg <- mapM (R.argMapM return (auxEvaluate (remainingFuel - 1) true)) args
                    -- And we create a branch by element of the cartesian product of the branches of the symbolic evaluation of the arguments.
                    mapM
                      ( \(fuel, newConds, args) ->
                          CstrBranch fuel
                            <$> normalizeTerm (R.appN (signatureSymbol f) args)
                            <*> return (andConstr conds newConds)
                      )
                      (cartesianSet resArg)
              -- If the head of the studied term is a destructor,
              -- then we creates branches.
              DDestructor _ -> do
                -- TODO: Currently the TyParams are completely dropped,
                -- ideally we should apply them to all the constructors when reconstructing the branches
                -- in order to allow translation to the SMT solver.
                Just (_, tyName, tyParams, studiedTerm, _, cases, excess) <- runMaybeT $ unDest t
                -- We symbolically evaluate the term we are studying.
                nconstr <- auxEvaluate (remainingFuel - 1) conds studiedTerm
                vars <- get
                -- We deshadow the terms, since the symbolic evaluation of the studied term could
                -- involve variable names present in those terms too.
                let cleanedCases = map (deshadowBoundNamesWithForbiddenNames (map fst vars)) cases
                let cleanedExcess = map (R.argMap id (deshadowBoundNamesWithForbiddenNames (map fst vars))) excess
                DTypeDef (Datatype _ _ _ consList) <- prtDefOf tyName
                concat
                  <$>
                  -- For each branch of the match, we create the associated constraint and
                  -- symbolically execute the result of this branch.
                  zipWithM
                    ( \(argCons, caseTerm) (cons, _) ->
                        concat
                          <$>
                          -- And we combine this with the constraints and terms obtained
                          -- during the symbolic execution of the studied term.
                          mapM
                            ( \(CstrBranch remFuel tx condx) -> do
                                modify (argCons ++)
                                newCond <-
                                  eqT
                                    remFuel
                                    tx
                                    ( R.appN
                                        (signatureSymbol cons)
                                        -- TODO: Here we would like to put the application of the constructor to the type parameters.
                                        (termOfConstructorVars argCons)
                                    )
                                let totalConds = andConstr condx newCond
                                vars <- get
                                smtResult <- lift $ sendToSMT totalConds vars
                                if smtResult
                                  then
                                    auxEvaluate
                                      (remainingFuel - 1)
                                      (andConstr condx newCond)
                                      =<< normalizeTerm (R.appN caseTerm cleanedExcess)
                                  else return []
                            )
                            nconstr
                    )
                    (map R.getHeadLams cleanedCases)
                    consList
              DTypeDef _ ->
                error "We do not expect name of inductive types here"
      where
        signatureSymbol x = R.App (R.F (FreeName x)) []
        -- Since we collected the name at the creation of the lambdas,
        -- the de Bruijn indices have to be computed.
        -- We do a double reversal of the list to put the index 0 to the inner-most one.
        termOfConstructorVars args =
          let reversedNameList = reverse (map fst args) in
          reverse $ zipWith (\x i -> R.Arg $ R.App (R.B (R.Ann x) i) []) reversedNameList [0..]
    auxEvaluate remainingFuel conds (R.Lam x ty u) = do
      modify ((R.ann x, ty) :)
      branches <- auxEvaluate remainingFuel conds u
      return $
        map (\(CstrBranch f t conds) -> CstrBranch f (R.Lam x ty t) conds) branches
    auxEvaluate remainingFuel conds (R.Abs ann _ t) =
      auxEvaluate remainingFuel conds t

cartesianSet :: [R.Arg a [CstrBranch]] -> [(Fuel, Constraint, [R.Arg a PirTerm])]
cartesianSet [] = [(NaturalEnd, true, [])]
cartesianSet (R.TyArg ty : tl) =
  map (\(f,c,l) ->  (f, c, R.TyArg ty :l)) (cartesianSet tl)
cartesianSet (R.Arg cstrState : tl) =
  concatMap
    ( \x@(CstrBranch remFuel t conds) ->
        map
          (\(f,c,l) -> (fuelOver remFuel f, andConstr conds c, R.Arg t :l))
          (cartesianSet tl)
    )
    cstrState

-- A term `t` verifies the predicate `isData` if it is composed only
-- of variables and type constructors (no destructors and no defined symbols).
isData :: (PirouetteReadDefs PlutusIR m) => PirTerm -> m Bool
isData (R.App hd args) = go hd args
  where
    go ::
      (PirouetteReadDefs PlutusIR m) =>
      R.Var Name (TermBase PlutusIR Name) ->
      [R.Arg PirType PirTerm] ->
      m Bool
    go (R.F (FreeName f)) args = do
      def <- prtDefOf f
      case def of
        DConstructor {} -> foldl' (\b t -> (&&) <$> b <*> studyArg t) (return True) args
        _ -> return False
    go _ args = foldl' (\b t -> (&&) <$> b <*> studyArg t) (return True) args
    studyArg ::
      (PirouetteReadDefs PlutusIR m) =>
      R.Arg PirType PirTerm ->
      m Bool
    studyArg (R.Arg t) = isData t
    studyArg (R.TyArg _) = return True
isData (R.Lam _ _ t) = isData t
isData (R.Abs _ _ t) = isData t

-- A very simple unification test.
-- If two terms are constructor-headed with different constructors,
-- then the constraint boils down to false.
-- Otherwise, we replace `C x1 x2 == C y1 y2` by the constraints
-- `x1 |-> y1` and `x2 |-> y2`.

-- TODO: We could be even more clever and inline the constraint `x |-> t` in the other constraints
-- (or even in the term we are executing) to do more pruning of inaccessible branches.
-- This raises a question, what is the job of this module, and the one of the SMT solver?
-- I have the feeling that doing it is steping on the feet of the SMT solver.
eqT ::
  PirouetteReadDefs PlutusIR m =>
  Fuel ->
  PirTerm ->
  PirTerm ->
  m Constraint
eqT OutOfFuel t@((R.App (R.B (R.Ann x) _) [])) u = do
  uData <- isData u
  if uData
  then return $ Assign x u
  else return $ OutOfFuelEq t u
eqT NaturalEnd (R.App (R.B (R.Ann x) _) []) u =
  return $ Assign x u
eqT remFuel t@(R.App (R.F (FreeName f)) argsF) u@(R.App (R.F (FreeName g)) argsG) = do
  defF <- prtDefOf f
  defG <- prtDefOf g
  case (defF, defG) of
    (DConstructor {}, DConstructor {}) ->
      if f == g
        then
          And <$>
            zipWithM
              -- Since argsG is constructed by applying the nth constructor of the datatype we are destructing,
              -- to the variables which are under the lambda abstractions,
              -- we know that the symbol we are dealing with is a bound variable which is not applied.
              -- Hence, we have the guarantee that it is not a type argument.
              -- This justifies our unsafe matching.
              (\(R.Arg t) (R.Arg u) -> eqT remFuel t u)
              argsG
              (filter R.isArg argsF)
        else return Bot
    _ -> return $ NonInlinableSymbolEq t u
eqT _ t u = return $ NonInlinableSymbolEq t u

-}
