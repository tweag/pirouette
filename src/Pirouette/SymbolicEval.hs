{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.SymbolicEval where

import Control.Monad
import Control.Monad.State
import Data.Bifunctor (bimap, first, second)
import Data.List (concat, concatMap, elemIndex, foldl', intersperse)
import Data.Maybe (mapMaybe)
import Data.Text.Prettyprint.Doc hiding (Pretty (..))
import Data.Void (absurd)
import Debug.Trace (trace)
import Pirouette.Monad
import Pirouette.Monad.Logger
import Pirouette.Monad.Maybe
import Pirouette.PlutusIR.Utils
import Pirouette.SMT (smtCheckPathConstraint)
import Pirouette.SMT.Constraints (Constraint (..))
import qualified Pirouette.SMT.SimpleSMT as SmtLib (Result (..))
import Pirouette.Term.FromPlutusIR ()
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Term.Transformations
import qualified Data.Map as Map

-- The result of symbolically executing `f arg1 arg2 arg3`
-- is a list of branches.
data SymbRes = SymbRes Name [Name] [CstrBranch]

instance Pretty SymbRes where
  pretty (SymbRes f args cstr) =
    "When evaluating" <+> pretty f
      <+> mconcat (intersperse " " (map pretty args))
      <> "\n"
      <> pretty cstr

-- A branch of the symbolic execution is a result term and
-- the constraint to fulfill to reach this branch.
data CstrBranch = CstrBranch PrtTerm Constraint

instance Pretty CstrBranch where
  pretty (CstrBranch t conds) =
    "If:\n" <> indent 2 (pretty conds)
      <> "\nthe output is:\n"
      <> indent 2 (pretty t)

instance Pretty Constraint where
  pretty (Assign n term) =
    pretty n <+> "↦" <+> pretty term
  pretty (OutOfFuelEq t u) =
    pretty t <+> "==" <+> pretty u
  pretty Bot =
    "⊥"
  pretty (And []) =
    "⊤"
  pretty (And l) =
    mconcat $ intersperse "\n∧ " (map pretty l)

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

sendToSMT :: (MonadIO m, PirouetteDepOrder m) => Constraint -> [(Name, PrtType)] -> m Bool
sendToSMT Bot _ = return False
sendToSMT (And []) _ = return True
sendToSMT constr env =
  do
    smtResult <- smtCheckPathConstraint (Map.fromList env) constr
    return $
      case smtResult of
        SmtLib.Unsat -> False
        _ -> True

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
  PirouetteReadDefs m =>
  PrtTerm ->
  PrtTerm ->
  m Constraint
eqT t@(R.App (R.B (R.Ann x) _) []) u = do
  return $ Assign x u
eqT t@(R.App (R.F (FreeName f)) argsF) u@(R.App (R.F (FreeName g)) argsG) = do
  defF <- prtDefOf f
  defG <- prtDefOf g
  case (defF, defG) of
    (DConstructor {}, DConstructor {}) ->
      if f == g
        then return $ And (zipWith assigns argsG (filter isntType argsF))
        else return Bot
    _ -> return $ OutOfFuelEq t u
  where
    isntType (R.Arg _) = True
    isntType (R.TyArg _) = False

    -- Since argsG is constructed by applying the nth constructor of the datatype we are destructing,
    -- to the variables which are under the lambda abstractions
    assigns (R.Arg (R.App (R.F (FreeName x)) [])) (R.Arg t) =
      Assign x t
eqT t u = return $ OutOfFuelEq t u

-- The main function. It takes a function name and its definition and output a result of symbolic execution.
-- Since we are doing inlining, we access symbol definition,
-- so this output is in a `PirouetteReadDefs` monad.
evaluate :: (PirouetteDepOrder m, MonadIO m) => Name -> PrtTerm -> m SymbRes
evaluate = auxEvaluateInputs []
  where
    -- We try to inline everything
    -- We do at most `fuel` inlining. After it, the symbolic evaluation of `t` simply output
    -- `CstrBranch t true`.
    mainFuel :: Int
    mainFuel = 10

    -- The first step is to collect the arguments of the function in a list of name.
    auxEvaluateInputs ::
      (PirouetteDepOrder m, MonadIO m) =>
      [(Name, PrtType)] ->
      Name ->
      PrtTerm ->
      m SymbRes
    auxEvaluateInputs vars mainFun t@(R.App _ _) =
      SymbRes mainFun (map fst vars) <$> evalStateT (auxEvaluate mainFuel true t) vars
    auxEvaluateInputs vars mainFun (R.Lam a ty t) =
      auxEvaluateInputs ((R.ann a, ty) : vars) mainFun t
    auxEvaluateInputs vars mainFun (R.Abs a _ t) =
      auxEvaluateInputs vars mainFun t
    auxEvaluateInputs _ _ (R.Hole h) =
      absurd h

    -- Once all the names of the argument variables have been collected, we start the symbolic execution part.
    -- This is in a `State` monad, since the fuel for inlining and the names of already met variables should be shared between the symbolic evaluation of the different arguments of a function.
    auxEvaluate ::
      (PirouetteDepOrder m, MonadIO m) =>
      Int ->
      Constraint ->
      PrtTerm ->
      StateT [(Name, PrtType)] m [CstrBranch]
    auxEvaluate _ Bot _ = return []
    auxEvaluate remainingFuel conds t@(R.App hd args) = do
      vars <- get
      if remainingFuel == 0
        then -- If fuel is over, then we simply output the term as is.
          return [CstrBranch t conds]
        else case hd of
          -- TODO: In all those cases, is it interesting to symbolically evaluate the arguments?
          R.B (R.Ann _) _ -> return [CstrBranch t conds]
          R.F (Constant _) -> return [CstrBranch t conds]
          R.F (Builtin _) -> return [CstrBranch t conds]
          R.F Bottom -> return [CstrBranch t conds]
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
                  [] -> return [CstrBranch (R.appN (var f) []) conds]
                  _ -> do
                    -- Else we symbolically execute the arguments.
                    resArg <- mapM (R.argMapM return (auxEvaluate (remainingFuel - 1) true)) args
                    -- And we create a branch by element of the cartesian product of the branches of the symbolic evaluation of the arguments.
                    mapM
                      ( \(newConds, args) ->
                          CstrBranch
                            <$> normalizeTerm (R.appN (var f) args)
                            <*> return (andConstr conds newConds)
                      )
                      (cartesianSet resArg)
              -- If the head of the studied term is a destructor,
              -- then we creates branches.
              DDestructor _ -> do
                Just (_, tyName, _, studiedTerm, _, cases, excess) <- runMaybeT $ unDest t
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
                            ( \(CstrBranch tx condx) -> do
                                modify (argCons ++)
                                newCond <-
                                  eqT
                                    tx
                                    ( R.appN
                                        (var cons)
                                        (map (R.Arg . var . fst) argCons)
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
        var x = R.App (R.F (FreeName x)) []
    auxEvaluate remainingFuel conds (R.Lam x ty u) = do
      modify ((R.ann x, ty) :)
      branches <- auxEvaluate remainingFuel conds u
      return $
        map (\(CstrBranch t conds) -> CstrBranch (R.Lam x ty t) conds) branches
    auxEvaluate remainingFuel conds (R.Abs ann _ t) =
      auxEvaluate remainingFuel conds t
    auxEvaluate _ _ (R.Hole h) =
      absurd h

cartesianSet :: [R.Arg a [CstrBranch]] -> [(Constraint, [R.Arg a PrtTerm])]
cartesianSet [] = [(true, [])]
cartesianSet (R.TyArg ty : tl) =
  map (second (R.TyArg ty :)) (cartesianSet tl)
cartesianSet (R.Arg cstrState : tl) =
  concatMap
    ( \x@(CstrBranch t conds) ->
        map
          (bimap (andConstr conds) (R.Arg t :))
          (cartesianSet tl)
    )
    cstrState

runEvaluation ::
  (PirouetteDepOrder m, MonadIO m) =>
  Name ->
  PrtTerm ->
  m SymbRes
runEvaluation n t =
  evaluate n =<< normalizeTerm t

normalizeTerm ::
  (PirouetteReadDefs m) =>
  PrtTerm ->
  m PrtTerm
normalizeTerm = destrNF >=> removeExcessiveDestArgs >=> constrDestrId

-- A term `t` verifies the predicate `isTermCons` if it is composed only
-- of variables and type constructors (no destructors and no defined symbols).
isTermCons :: (PirouetteReadDefs m) => PrtTerm -> m Bool
isTermCons (R.App hd args) = go hd args
  where
    go ::
      (PirouetteReadDefs m) =>
      R.Var Name (PIRBase fun Name) ->
      [R.Arg PrtType PrtTerm] ->
      m Bool
    go (R.F (FreeName f)) args = do
      def <- prtDefOf f
      case def of
        DConstructor {} -> foldl' (\b t -> (&&) <$> b <*> studyArg t) (return True) args
        _ -> return False
    go _ args = foldl' (\b t -> (&&) <$> b <*> studyArg t) (return True) args
    studyArg ::
      (PirouetteReadDefs m) =>
      R.Arg PrtType PrtTerm ->
      m Bool
    studyArg (R.Arg t) = isTermCons t
    studyArg (R.TyArg _) = return True
isTermCons (R.Lam _ _ t) = isTermCons t
isTermCons (R.Abs _ _ t) = isTermCons t
isTermCons (R.Hole h) = absurd h
