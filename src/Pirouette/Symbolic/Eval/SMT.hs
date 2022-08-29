{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This is Pirouette's symbolic engine SMT solver interface. Inside the
--  "Pirouette.Symbolic.Eval" namespace, this should be the only module that explicitely
--  imports anything from the "Pirouette.SMT" namespace. Any additional needs from the symbolic
--  engine should be encoded as a 'SolverProblem'.
--
--  You probably will never need to import anything under the @SMT/@ folder explicitely unless
--  you're trying to do some very specific things or declaring a language.
--  If you're declaring a language you probably want only "Pirouette.SMT.Base" and "PureSMT" to bring the necessary
--  classes and definitions in scope. Check "Language.Pirouette.PlutusIR.SMT" for an example.
module Pirouette.Symbolic.Eval.SMT where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor (bimap)
import qualified Data.Kind as K
import qualified Data.List as List
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Pirouette.Monad
import Pirouette.SMT
import Pirouette.Symbolic.Eval.Types
import Pirouette.Term.Syntax
import Prettyprinter (align, enclose, vsep, (<+>))
import qualified PureSMT

-- | Contains the shared context of a session with the solver. Datatypes will
-- be declared first, then the uninterpreted functions. Definitions will
-- be declared in the same order they are provided.
data SolverSharedCtx lang = SolverSharedCtx
  { -- | List of datatypes to be declared
    solverCtxDatatypes :: [(Name, TypeDef lang)],
    -- | List of functions to be declared as uninterpreted functions.
    solverCtxUninterpretedFuncs :: [(Name, ([PureSMT.SExpr], PureSMT.SExpr))]
  }

solverSharedCtxUsedNames :: SolverSharedCtx lang -> S.Set Name
solverSharedCtxUsedNames (SolverSharedCtx tys fns) =
  S.fromList $ concatMap (\(n, tdef) -> n : map fst (constructors tdef)) tys ++ map fst fns

-- TODO: What is this for? The name is a little too general
data UniversalAxiom lang = UniversalAxiom
  { boundVars :: [(Name, Type lang)],
    axiomBody :: [PureSMT.SExpr] -> PureSMT.SExpr
  }

-- | The symbolic engine currently needs to call the SMT solver for two different problems:
--
--   1. Check whether a path is plausible
--   2. Check whether a certain property currently holds over a given path
data SolverProblem lang :: K.Type -> K.Type where
  CheckProperty :: (LanguagePretty lang) => CheckPropertyProblem lang -> SolverProblem lang PruneResult
  CheckPath :: CheckPathProblem lang -> SolverProblem lang Bool

data CheckPropertyProblem lang = CheckPropertyProblem
  { cpropOut :: PureSMT.SExpr,
    cpropIn :: Maybe PureSMT.SExpr,
    cpropAxioms :: [UniversalAxiom lang],
    cpropState :: SymEvalSt lang,
    cpropDefs :: PrtOrderedDefs lang
  }

-- | The result of a 'CheckPropertyProblem' is one of the following options:
data PruneResult
  = -- | The assumptions are inconsistent (TODO: what does it mean? example!)
    PruneInconsistentAssumptions
  | -- | The SMT was able to prove that the implication holds in this branch
    PruneImplicationHolds
  | -- | The SMT found a counter-example to the implication
    PruneCounterFound Model
  | -- | The SMT is uncertain whether the implication holds or not
    PruneUnknown
  deriving (Eq, Show)

data CheckPathProblem lang = CheckPathProblem
  { cpathState :: SymEvalSt lang,
    cpathDefs :: PrtOrderedDefs lang
  }

-- | Models returned by the SMT solver
newtype Model = Model [(PureSMT.SExpr, PureSMT.Value)]
  deriving (Eq, Show)

instance Pretty Model where
  pretty (Model m) =
    let simplified = map (bimap (PureSMT.overAtomS f) (PureSMT.overAtomV f)) m
     in enclose "{ " " }" $ align (vsep [pretty n <+> "↦" <+> pretty term | (n, term) <- simplified])
    where
      -- remove 'pir_' from the values
      f "pir_Cons" = ":"
      f "pir_Nil" = "[]"
      f ('p' : 'i' : 'r' : '_' : rest) = rest
      f other = other

-- HACKS DUE TO #106: https://github.com/tweag/pirouette/issues/106
type HackSolver lang a = SolverT (ReaderT (PrtOrderedDefs lang) IO) a

hackSolver :: (MonadIO m) => PureSMT.Solver -> SolverT m a -> m a
hackSolver s = flip runReaderT s . unSolverT

hackSolverPrt :: PureSMT.Solver -> PrtOrderedDefs lang -> HackSolver lang a -> IO a
hackSolverPrt s defs = flip runReaderT defs . flip runReaderT s . unSolverT

-- | Instance necessary to call the 'PureSMT.solve' function.
instance (LanguageSMT lang) => PureSMT.Solve lang where
  type Ctx lang = SolverSharedCtx lang
  type Problem lang = SolverProblem lang
  initSolver SolverSharedCtx {..} s = hackSolver s $ do
    res <- runExceptT $ declareDatatypes solverCtxDatatypes
    case res of
      Left err -> error ("Couldn't declare datatypes: " ++ show err)
      Right _ -> mapM_ (uncurry declareRawFun) solverCtxUninterpretedFuncs

  solveProblem (CheckPath CheckPathProblem {..}) s =
    hackSolverPrt s cpathDefs $ pathIsPlausible cpathState
    where
      pathIsPlausible ::
        (LanguageSMT lang) =>
        SymEvalSt lang ->
        HackSolver lang Bool
      pathIsPlausible env = do
        solverPush
        decl <- runExceptT (declareVariables (sestGamma env))
        case decl of
          Right _ -> return ()
          Left err -> error err
        -- Here we do not care about the totality of the translation,
        -- since we want to prune unsatisfiable path.
        -- And if a partial translation is already unsat,
        -- so is the translation of the whole set of constraints.
        (_, _, pathConstraints) <- constraintSetToSExpr (sestKnownNames env) (sestConstraint env)
        void $ assertConstraint (sestKnownNames env) pathConstraints
        res <- checkSat
        solverPop
        return $ case res of
          Unsat -> False
          _ -> True
  solveProblem (CheckProperty CheckPropertyProblem {..}) s =
    hackSolverPrt s cpropDefs $ checkProperty cpropOut cpropIn cpropAxioms cpropState
    where
      -- Our aim is to prove that
      -- (pathConstraints /\ cOut) => cIn.
      -- This is equivalent to the unsatisfiability of
      -- pathConstraints /\ cOut /\ (not cIn).
      checkProperty ::
        (LanguageSMT lang, LanguagePretty lang) =>
        PureSMT.SExpr ->
        Maybe PureSMT.SExpr ->
        [UniversalAxiom lang] ->
        SymEvalSt lang ->
        HackSolver lang PruneResult
      checkProperty cOut cIn axioms env = do
        solverPush
        let vars = sestGamma env
        decl <- runExceptT (declareVariables vars)
        instantiateAxiomWithVars axioms env
        case decl of
          Right _ -> return ()
          Left err -> error err
        (_, _, pathConstraints) <- constraintSetToSExpr (sestKnownNames env) (sestConstraint env)
        (cstrTotal, _cstrUsedAnyUFs) <- assertConstraint (sestKnownNames env) pathConstraints
        (outTotal, _outUsedAnyUFs) <- assertConstraint (sestKnownNames env) cOut
        inconsistent <- checkSat
        case (inconsistent, cIn) of
          (Unsat, _) -> do
            solverPop
            return PruneInconsistentAssumptions
          (_, Nothing) -> do
            solverPop
            return PruneUnknown
          (_, Just cIn') -> do
            (inTotal, _inUsedAnyUFs) <- assertNotConstraint (sestKnownNames env) cIn'
            let everythingWasTranslated = cstrTotal && outTotal && inTotal
            -- Any usedAnyUFs = cstrUsedAnyUFs <> outUsedAnyUFs <> inUsedAnyUFs
            result <- checkSat
            -- liftIO $ print result
            -- liftIO $ print $ pretty (sestConstraint env)
            -- liftIO $ print (cstrTotal, outTotal, inTotal)
            finalResult <- case result of
              Unsat -> return PruneImplicationHolds
              -- If a partial translation of the constraints is SAT,
              -- it does not guarantee us that the full set of constraints is satisfiable.
              -- Only in the case in which we could translate the entire thing to prove.
              Sat | everythingWasTranslated -> do
                m <- if null vars then pure [] else getModel (M.keys vars)
                pure $ PruneCounterFound (Model m)
              _ -> return PruneUnknown
            solverPop
            return finalResult

assertConstraint,
  assertNotConstraint ::
    (PirouetteReadDefs lang m, LanguageSMT lang, MonadIO m) =>
    S.Set Name ->
    PureSMT.SExpr ->
    SolverT m (Bool, UsedAnyUFs)
assertConstraint = undefined
assertNotConstraint = undefined

{-
assertConstraint knownNames c@Bot = do
  (done, usedAnyUFs, expr) <- constraintToSExpr knownNames c
  assert expr
  pure (done, usedAnyUFs)
assertConstraint knownNames (And atomics) = do
  (dones, usedAnyUFs) <-
    unzip
      <$> forM
        atomics
        ( \atomic -> do
            -- do it one by one
            (done, usedAnyUFs, expr) <- constraintToSExpr knownNames (And [atomic])
            assert expr
            pure (done, usedAnyUFs)
        )
  pure (and dones, mconcat usedAnyUFs)
assertNotConstraint knownNames c = do
  (done, usedAnyUFs, expr) <- constraintToSExpr knownNames c
  assertNot expr
  pure (done, usedAnyUFs)
-}

-- TODO: why is this needed, what needs to be done on the TODO below?
instantiateAxiomWithVars ::
  (LanguageSMT lang, MonadIO m) => [UniversalAxiom lang] -> SymEvalSt lang -> SolverT m ()
instantiateAxiomWithVars axioms env =
  SolverT $ do
    solver <- ask
    liftIO $
      mapM_
        ( \(name, ty) ->
            mapM_
              ( \UniversalAxiom {..} ->
                  when (List.any (\(_, tyV) -> tyV == ty) boundVars) $
                    if length boundVars == 1
                      then void $ PureSMT.assert solver (axiomBody [PureSMT.symbol (toSmtName name)])
                      else error "Several universally bound variables not handled yet" -- TODO
              )
              axioms
        )
        (M.toList $ sestGamma env)
