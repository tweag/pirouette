{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This is Pirouette's SMT solver interface; you probably won't need to import
--  anything under the @SMT/@ folder explicitely unless you're trying to do some
--  very specific things or declaring a language. If you're declaring a language you probably
--  want only "Pirouette.SMT.Base" and "PureSMT" to bring the necessary
--  classes and definitions in scope. Check "Language.Pirouette.PlutusIR.SMT" for an example.
module Pirouette.Symbolic.Eval.SMT where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.List as List
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Pirouette.Monad
import Pirouette.Monad.Logger
import qualified Pirouette.SMT.Constraints as C
import Pirouette.SMT.FromTerm
import qualified Pirouette.SMT.Monadic as SMT
import Pirouette.Symbolic.Eval.Types
import Pirouette.Term.Syntax
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

data UniversalAxiom lang = UniversalAxiom
  { boundVars :: [(Name, Type lang)],
    axiomBody :: [PureSMT.SExpr] -> PureSMT.SExpr
  }

data CheckPropertyProblem lang = CheckPropertyProblem
  { cpropOut :: Constraint lang,
    cpropIn :: Maybe (Constraint lang),
    cpropAxioms :: [UniversalAxiom lang],
    cpropState :: SymEvalSt lang,
    cpropDefs :: PrtOrderedDefs lang
  }

data CheckPathProblem lang = CheckPathProblem
  { cpathState :: SymEvalSt lang,
    cpathDefs :: PrtOrderedDefs lang
  }

-- | Different queries that we know how to solve
data SolverProblem lang :: * -> * where
  CheckProperty :: (LanguagePretty lang) => CheckPropertyProblem lang -> SolverProblem lang PruneResult
  CheckPath :: CheckPathProblem lang -> SolverProblem lang Bool

newtype Model = Model [(PureSMT.SExpr, PureSMT.Value)]
  deriving (Eq, Show)

data EvaluationWitness lang
  = Verified
  | Discharged
  | CounterExample (TermMeta lang SymVar) Model
  deriving (Eq, Show)

data PruneResult
  = PruneInconsistentAssumptions
  | PruneImplicationHolds
  | PruneCounterFound Model
  | PruneUnknown
  deriving (Eq, Show)

-- HACKS DUE TO #106: https://github.com/tweag/pirouette/issues/106
type HackSolver lang a = SMT.SolverT (ReaderT (PrtOrderedDefs lang) (PrtT IO)) a

hackSolver :: (MonadIO m) => PureSMT.Solver -> SMT.SolverT m a -> m a
hackSolver s = flip runReaderT s . SMT.unSolverT

hackSolverPrt :: PureSMT.Solver -> PrtOrderedDefs lang -> HackSolver lang a -> IO a
hackSolverPrt s defs = wrap <=< (mockPrtT . flip runReaderT defs . flip runReaderT s . SMT.unSolverT)
  where
    wrap :: (Either String a, [LogMessage]) -> IO a
    wrap (Left err, _) = error err
    wrap (Right a, _) = return a

instance (SMT.LanguageSMT lang) => PureSMT.Solve lang where
  type Ctx lang = SolverSharedCtx lang
  type Problem lang = SolverProblem lang
  initSolver SolverSharedCtx {..} s = hackSolver s $ do
    _ <- runExceptT $ SMT.declareDatatypes solverCtxDatatypes
    mapM_ (uncurry SMT.declareRawFun) solverCtxUninterpretedFuncs

  solveProblem (CheckPath CheckPathProblem {..}) s =
    hackSolverPrt s cpathDefs $ pathIsPlausible cpathState
    where
      pathIsPlausible ::
        (SMT.LanguageSMT lang) =>
        SymEvalSt lang ->
        HackSolver lang Bool
      pathIsPlausible env
        | sestValidated env = return True -- We already validated this branch before; nothing new was learnt.
        | otherwise = do
          SMT.solverPush
          decl <- runExceptT (SMT.declareVariables (sestGamma env))
          case decl of
            Right _ -> return ()
            Left err -> error err
          -- Here we do not care about the totality of the translation,
          -- since we want to prune unsatisfiable path.
          -- And if a partial translation is already unsat,
          -- so is the translation of the whole set of constraints.
          void $ assertConstraint (sestKnownNames env) (sestConstraint env)
          res <- SMT.checkSat
          SMT.solverPop
          return $ case res of
            SMT.Unsat -> False
            _ -> True
  solveProblem (CheckProperty CheckPropertyProblem {..}) s =
    hackSolverPrt s cpropDefs $ checkProperty cpropOut cpropIn cpropAxioms cpropState
    where
      -- Our aim is to prove that
      -- (pathConstraints /\ cOut) => cIn.
      -- This is equivalent to the unsatisfiability of
      -- pathConstraints /\ cOut /\ (not cIn).
      checkProperty ::
        (SMT.LanguageSMT lang, LanguagePretty lang) =>
        Constraint lang ->
        Maybe (Constraint lang) ->
        [UniversalAxiom lang] ->
        SymEvalSt lang ->
        HackSolver lang PruneResult
      checkProperty cOut cIn axioms env = do
        SMT.solverPush
        let vars = sestGamma env
        decl <- runExceptT (SMT.declareVariables vars)
        instantiateAxiomWithVars axioms env
        case decl of
          Right _ -> return ()
          Left err -> error err
        (cstrTotal, _cstrUsedAnyUFs) <- assertConstraint (sestKnownNames env) (sestConstraint env)
        (outTotal, _outUsedAnyUFs) <- assertConstraint (sestKnownNames env) cOut
        inconsistent <- SMT.checkSat
        case (inconsistent, cIn) of
          (SMT.Unsat, _) -> do
            SMT.solverPop
            return PruneInconsistentAssumptions
          (_, Nothing) -> do
            SMT.solverPop
            return PruneUnknown
          (_, Just cIn') -> do
            (inTotal, _inUsedAnyUFs) <- assertNotConstraint (sestKnownNames env) cIn'
            let everythingWasTranslated = cstrTotal && outTotal && inTotal
            -- Any usedAnyUFs = cstrUsedAnyUFs <> outUsedAnyUFs <> inUsedAnyUFs
            result <- SMT.checkSat
            -- liftIO $ print result
            -- liftIO $ print $ pretty (sestConstraint env)
            -- liftIO $ print (cstrTotal, outTotal, inTotal)
            finalResult <- case result of
              SMT.Unsat -> return PruneImplicationHolds
              -- If a partial translation of the constraints is SAT,
              -- it does not guarantee us that the full set of constraints is satisfiable.
              -- Only in the case in which we could translate the entire thing to prove.
              SMT.Sat | everythingWasTranslated -> do
                m <- if null vars then pure [] else SMT.getModel (M.keys vars)
                pure $ PruneCounterFound (Model m)
              _ -> return PruneUnknown
            SMT.solverPop
            return finalResult

assertConstraint,
  assertNotConstraint ::
    (PirouetteReadDefs lang m, SMT.LanguageSMT lang, SMT.ToSMT meta, MonadIO m) =>
    S.Set Name ->
    C.Constraint lang meta ->
    SMT.SolverT m (Bool, UsedAnyUFs)
assertConstraint knownNames c@C.Bot = do
  (done, usedAnyUFs, expr) <- C.constraintToSExpr knownNames c
  SMT.assert expr
  pure (done, usedAnyUFs)
assertConstraint knownNames (C.And atomics) = do
  (dones, usedAnyUFs) <-
    unzip
      <$> forM
        atomics
        ( \atomic -> do
            -- do it one by one
            (done, usedAnyUFs, expr) <- C.constraintToSExpr knownNames (C.And [atomic])
            SMT.assert expr
            pure (done, usedAnyUFs)
        )
  pure (and dones, mconcat usedAnyUFs)
assertNotConstraint knownNames c = do
  (done, usedAnyUFs, expr) <- C.constraintToSExpr knownNames c
  SMT.assertNot expr
  pure (done, usedAnyUFs)

instantiateAxiomWithVars ::
  (SMT.LanguageSMT lang, MonadIO m) => [UniversalAxiom lang] -> SymEvalSt lang -> SMT.SolverT m ()
instantiateAxiomWithVars axioms env =
  SMT.SolverT $ do
    solver <- ask
    liftIO $
      mapM_
        ( \(name, ty) ->
            mapM_
              ( \UniversalAxiom {..} ->
                  when (List.any (\(_, tyV) -> tyV == ty) boundVars) $
                    if length boundVars == 1
                      then void $ PureSMT.assert solver (axiomBody [PureSMT.symbol (SMT.toSmtName name)])
                      else error "Several universally bound variables not handled yet" -- TODO
              )
              axioms
        )
        (M.toList $ sestGamma env)
