{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Pirouette.SymbolicEval where

import Control.Monad
import Control.Monad.State
import Data.List (foldl', intersperse)
import qualified Data.Map as Map
import Data.Text.Prettyprint.Doc hiding (Pretty (..))
import Data.Void (absurd)
import Pirouette.Monad
import Pirouette.Monad.Maybe
import Pirouette.PlutusIR.Utils
import Pirouette.SMT (smtCheckPathConstraint)
import Pirouette.SMT.Constraints (Constraint (..))
import qualified Pirouette.SMT.SimpleSMT as SmtLib (Result (..))
import Pirouette.Term.FromPlutusIR (PlutusIR, PirTerm, PirType)
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.Transformations
import Control.Monad.Reader
import Control.Monad.Except
import Control.Applicative
import Data.Data hiding (eqT)
import Control.Arrow (first)
import qualified Data.Map.Strict as M
import ListT

type SymEvalT lang m = ReaderT (SymEvalEnv lang) (ListT m)

data SymEvalEnv lang = SymEvalEnv
  { seeFuel :: Integer
  , seeConstraint :: Constraint
  , seeEnv :: M.Map Name (PrtType lang)
  }

runSymEvalT :: (Monad m) => Integer -> SymEvalT lang m a -> m [a]
runSymEvalT maxFuel = toList . flip runReaderT env0
  where
    env0 :: SymEvalEnv lang
    env0 = SymEvalEnv maxFuel (And []) M.empty

class (PirouetteDepOrder lang m, MonadPlus m, MonadReader (SymEvalEnv lang) m)
    => MonadSymEval lang m where
  -- |Extends the environment with a number of declared symbolic variables
  withSymVars :: [(Name, PrtType lang)] -> ([SymVar] -> m a) -> m a

instance PirouetteReadDefs lang m => PirouetteReadDefs lang (SymEvalT lang m) where
  prtAllDefs = lift $ lift prtAllDefs
  prtMain = lift $ lift prtMain

instance PirouetteDepOrder lang m => PirouetteDepOrder lang (SymEvalT lang m) where
  prtDependencyOrder = lift $ lift prtDependencyOrder

instance (PirouetteDepOrder lang m) => MonadSymEval lang (SymEvalT lang m) where
  withSymVars = undefined

data Path lang
  = Complete { pathConstraint :: Constraint,
               pathResult :: PrtTerm lang
             }
  | Partial { pathConstraint :: Constraint,
              pathCurrent :: PrtTermMeta lang SymVar
            }

newtype SymVar = SymVar { symVar :: Name }
 deriving (Eq, Show, Data, Typeable)

runEvaluation ::
  (MonadSymEval lang m) =>
  Term lang Name ->
  m (Path lang)
runEvaluation t = do
  let (lams, body) = R.getHeadLams t
  withSymVars lams $ \svars ->
    runEvaluation' (R.appN (prtTermToMeta body) $ map (R.Arg . (`R.App` []) . R.M) svars)

runEvaluation' ::
  (MonadSymEval lang m) =>
  TermMeta lang SymVar Name ->
  m (Path lang)
runEvaluation' t = symeval =<< normalizeTerm t
  -- evaluate n =<< normalizeTerm t

normalizeTerm ::
  (PirouetteReadDefs lang m) =>
  TermMeta lang SymVar Name ->
  m (TermMeta lang SymVar Name)
normalizeTerm = destrNF >=> removeExcessiveDestArgs >=> constrDestrId

symeval ::
  (MonadSymEval lang m) =>
  TermMeta lang SymVar Name ->
  m (Path lang)
-- We cannot symbolic-evaluate polymorphic terms
symeval R.Abs {} = error "Can't symbolically evaluate polymorphic things"
-- If we're forced to symbolic evaluate a lambda, we create a new metavariable
-- and evaluate the corresponding application.
symeval t@(R.Lam (R.Ann x) ty body) = do
  let ty' = prtTypeFromMeta ty
  withSymVars [(x, ty')] $ \[svars] ->
    symeval $ t `R.app` R.Arg (R.App (R.M svars) [])
-- If we're evaluating an applcation, we distinguish between a number
-- of constituent cases:
symeval t = do
  -- We start by ensuring that our current path constraint is satisfiable;
  constr <- getPathConstraintIfSAT
  -- Next we check if this is a branch that still has fuel to proceed
  fuelLeft <- asks seeFuel
  if fuelLeft <= 0
  then return $ Partial constr t
  else undefined

getPathConstraintIfSAT :: (MonadSymEval lang m) => m Constraint
getPathConstraintIfSAT = do
  constr <- asks seeConstraint
  env <- asks seeEnv
  plausibleBranch <- sendToSMT constr env
  guard plausibleBranch
  return constr

sendToSMT :: (MonadSymEval lang m) => Constraint -> M.Map Name (PrtType lang) -> m Bool
sendToSMT Bot _ = return False
sendToSMT (And []) _ = return True
sendToSMT constr env = return True
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

-- Essentially list concatenation, with the specificity that `Bot` is absorbing.
andConstr :: Constraint -> Constraint -> Constraint
andConstr Bot _ = Bot
andConstr _ Bot = Bot
andConstr (And l) (And m) = And (l ++ m)
andConstr (And l) y = And (y : l)
andConstr x (And m) = And (x : m)
andConstr x y = And [x, y]

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
-- `x1 ↦ y1` and `x2 ↦ y2`.

-- TODO: We could be even more clever and inline the constraint `x ↦ t` in the other constraints
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
