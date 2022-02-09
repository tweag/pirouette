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

module Pirouette.Term.Symbolic.Eval where

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
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.Transformations

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Show, Data, Typeable)

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

data PathStatus = Completed | OutOfFuel

data Path lang res = Path
  { pathConstraint :: Constraint lang,
    pathGamma :: M.Map Name (PrtType lang),
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

data SymEvalSt lang = SymEvalSt
  { sestConstraint :: Constraint lang,
    sestGamma :: M.Map Name (PrtType lang),
    sestFreshCounter :: Int,
    sestFuel :: Int
  }

-- |Given a result and a resulting state, returns a 'Path' representing it.
path :: a -> SymEvalSt lang -> Path lang a
path x st = Path
  { pathConstraint = sestConstraint st
  , pathGamma = sestGamma st
  , pathStatus = if sestFuel st <= 0 then OutOfFuel else Completed
  , pathResult = x
  }

newtype SymEvalT lang m a = SymEvalT {symEvalT :: StateT (SymEvalSt lang) (ListT m) a}
  deriving (Functor)
  deriving newtype (Applicative, Monad, MonadState (SymEvalSt lang))

symevalT :: (Monad m) => SymEvalT lang m a -> m [Path lang a]
symevalT = runSymEvalT st0
  where
    st0 = SymEvalSt mempty M.empty 0 10

runSymEvalTRaw :: (Monad m) => SymEvalSt lang -> SymEvalT lang m a -> ListT m (a, SymEvalSt lang)
runSymEvalTRaw st = flip runStateT st . symEvalT

runSymEvalT :: (Monad m) => SymEvalSt lang -> SymEvalT lang m a -> m [Path lang a]
runSymEvalT st = ListT.toList . fmap (uncurry path) . runSymEvalTRaw st

instance (Monad m) => Alternative (SymEvalT lang m) where
  empty = SymEvalT $ StateT $ const empty
  xs <|> ys = SymEvalT $ StateT $ \st -> runSymEvalTRaw st xs <|> runSymEvalTRaw st ys

instance MonadTrans (SymEvalT lang) where
  lift = SymEvalT . lift . lift

instance (MonadFail m) => MonadFail (SymEvalT lang m) where
  fail = lift . fail

type SymEvalConstr lang m = (PirouetteDepOrder lang m, PrettyLang lang, MonadIO m)

instance (MonadIO m) => MonadIO (SymEvalT lang m) where
  liftIO = lift . liftIO

-- |Prune the set of paths in the current set.
prune :: (SymEvalConstr lang m) => SymEvalT lang m a -> SymEvalT lang m a
prune xs = SymEvalT $ StateT $ \st -> do
    (x, st') <- runSymEvalTRaw st xs
    ok <- lift $ pathIsPlausible x st'
    guard ok
    return (x, st')
  where
    pathIsPlausible :: (Monad m) => a -> SymEvalSt lang -> m Bool
    pathIsPlausible p env = return True -- TODO: send path constraint to SMT?

-- |Learn a new constraint and add it as a conjunct to the set of constraints of
-- the current path.
learn :: (SymEvalConstr lang m) => Constraint lang -> SymEvalT lang m ()
learn c = modify (\st -> st { sestConstraint = c <> sestConstraint st })

declSymVars :: (SymEvalConstr lang m) => [(Name, PrtType lang)] -> SymEvalT lang m [SymVar]
declSymVars vs = do
  old <- get
  modify (\st -> st { sestGamma = M.union (sestGamma st) (M.fromList vs) })
  return $ map (SymVar . fst) vs

freshSymVar :: (SymEvalConstr lang m) => PrtType lang -> SymEvalT lang m SymVar
freshSymVar ty = head <$> freshSymVars [ty]

freshSymVars :: (SymEvalConstr lang m) => [PrtType lang] -> SymEvalT lang m [SymVar]
freshSymVars [] = return []
freshSymVars tys = do
  let n = length tys
  ctr <- gets sestFreshCounter
  modify (\st -> st { sestFreshCounter = sestFreshCounter st + n })
  let vars = zipWith (\i ty -> (Name "s" (Just i) , ty)) [ctr..] tys
  declSymVars vars

runEvaluation :: (SymEvalConstr lang m) => Term lang Name -> SymEvalT lang m (TermMeta lang SymVar Name)
runEvaluation t = do
  liftIO $ putStrLn $ "evaluating: " ++ show (pretty t)
  let (lams, body) = R.getHeadLams t
  svars <- declSymVars lams
  symeval (R.appN (prtTermToMeta t) $ map (R.Arg . (`R.App` []) . R.M) svars)

consumeGas :: (SymEvalConstr lang m) => SymEvalT lang m a -> SymEvalT lang m a
consumeGas f = modify (\st -> st { sestFuel = sestFuel st - 1 }) >> f

currentGas :: (SymEvalConstr lang m) => SymEvalT lang m Int
currentGas = gets sestFuel

normalizeTerm :: (SymEvalConstr lang m) => TermMeta lang SymVar Name -> m (TermMeta lang SymVar Name)
normalizeTerm = destrNF >=> removeExcessiveDestArgs >=> constrDestrId

symeval :: (SymEvalConstr lang m) => TermMeta lang SymVar Name -> SymEvalT lang m (TermMeta lang SymVar Name)
symeval t = do
  t' <- lift $ normalizeTerm t
  fuelLeft <- currentGas
  if fuelLeft <= 0
    then return t'
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
  [svars] <- declSymVars [(x, ty')]
  symeval' $ t `R.app` R.Arg (R.App (R.M svars) [])
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
        svar <- freshSymVar ty
        learn (svar :== term') -- TODO: instead of this learn, we can try unifying with symbCons below:
        asum $ for2 consList cases $ \(consName, consTy) term -> do
          let (consArgs, res) = R.tyFunArgs consTy
          svars <- freshSymVars consArgs
          let symbCons =
                R.App (R.F $ FreeName consName) $
                  map (R.TyArg . prtTypeToMeta) tyParams' ++ map (R.Arg . (`R.App` []) . R.M) svars
          learn (svar :== symbCons)
          consumeGas $ symeval term

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 as bs f = zipWith f as bs

--- TMP CODE

instance (PrettyLang lang, Pretty a) => Pretty (Path lang a) where
  pretty (Path conds gamma ps res) =
    vsep [ "With:" <+> pretty (M.toList gamma)
         , "If:" <+> indent 2 (pretty conds)
         , "Status:" <+> pretty ps
         , "Result:" <+> indent 2 (pretty res)
         ]

instance Pretty PathStatus where
  pretty Completed = "Completed"
  pretty OutOfFuel = "OutOfFuel"

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

-- OLD CODE:

{-

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
