{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.Symbolic.Prover where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Text as T
import Pirouette.Monad (termIsWHNFOrMeta)
import Pirouette.SMT.Base (LanguageSMT (isStuckBuiltin))
import Pirouette.SMT.Constraints
import Pirouette.SMT.SimpleSMT (SExpr (..))
import Pirouette.SMT.Translation
import Pirouette.Term.Symbolic.Eval
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R

-- | A problem represents a triple that should be checked.
-- It should be the case that assuming 'problemAssume',
-- the execution of 'problemTerm' always leaves us in a
-- scenario in which 'problemProve' holds.
--
-- It *must* be the case that 'problemAssume' and 'problemProve'
-- have the right type, in particular they should take an
-- additional *first* argument for the type of the result,
-- and then as many arguments as 'problemBody' has.
data Problem lang = Problem
  { problemResultTy :: Type lang,
    problemBody :: Term lang,
    problemAssume :: Term lang,
    problemProve :: Term lang
  }
  deriving (Eq, Show)

type SymTerm lang = TermMeta lang SymVar

rESULTNAME :: Name
rESULTNAME = "__result"

prove ::
  (SymEvalConstr lang m, MonadIO m) =>
  StoppingCondition ->
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
prove shouldStop problem = symevalT shouldStop $ proveRaw problem

proveAny ::
  (SymEvalConstr lang m, MonadIO m) =>
  StoppingCondition ->
  (Path lang (EvaluationWitness lang) -> Bool) ->
  Problem lang ->
  m (Maybe (Path lang (EvaluationWitness lang)))
proveAny shouldStop p problem = symevalAnyPath shouldStop p $ proveRaw problem

proveRaw ::
  forall lang m.
  SymEvalConstr lang m =>
  Problem lang ->
  SymEvalT lang m (EvaluationWitness lang)
proveRaw Problem {..} = do
  -- get types for lambdas
  let (lams, _) = R.getHeadLams problemBody
  -- declare new symbolic variables
  argVars <- declSymVars lams
  [resultVar] <- declSymVars [(rESULTNAME, problemResultTy)]
  let allVars = resultVar : argVars
  -- create the new three terms
  let bodyTerm = createTerm problemBody argVars
      assumeTerm = createTerm problemAssume allVars
      proveTerm = createTerm problemProve allVars
  -- now we start the loop
  let smtVarNames = map (("pir_" <>) . T.unpack . nameString . symVar) allVars
  refineWitness smtVarNames <$> worker resultVar bodyTerm assumeTerm proveTerm
  where
    createTerm :: Term lang -> [SymVar] -> SymTerm lang
    createTerm body vars =
      R.appN (termToMeta body) $ map (R.TermArg . (`R.App` []) . R.Meta) vars
    -- only keep the variables we are interested about
    refineWitness allVars (CounterExample tm (Model m)) =
      CounterExample tm (Model [(Atom n, t) | (Atom n, t) <- m, n `elem` allVars])
    refineWitness _ w = w

worker ::
  forall lang m.
  SymEvalConstr lang m =>
  SymVar ->
  SymTerm lang ->
  SymTerm lang ->
  SymTerm lang ->
  SymEvalT lang m (EvaluationWitness lang)
worker resultVar bodyTerm assumeTerm proveTerm = do
  -- liftIO $ putStrLn "ONE STEP"
  -- liftIO $ print (pretty bodyTerm)
  -- liftIO $ print (pretty assumeTerm)
  -- liftIO $ print (pretty proveTerm)
  -- gets sestConstraint >>= liftIO . print . pretty
  -- _ <- liftIO getLine

  -- terms are only useful if they are in WHNF or are stuck
  -- (stuck-ness if defined per language)
  knownNames <- gets sestKnownNames
  let translate t = do
        res <- runTranslator $ translateTerm knownNames t
        isWHNF <- termIsWHNFOrMeta t
        case res of
          Left e -> pure $ Left e
          Right (c, _)
            | isStuckBuiltin t || isWHNF ->
              pure $ Right c
            | otherwise ->
              pure $ Left "not stuck term"
  -- step 1. try to prune the thing
  mayBodyTerm <- translate bodyTerm
  mayAssumeCond <- translate assumeTerm
  mayProveCond <- translate proveTerm
  -- introduce the assumption about the result, if useful
  case mayBodyTerm of
    Right _ -> learn $ And [Assign resultVar bodyTerm]
    _ -> pure ()
  -- liftIO $ print $ pretty (mayBodyTerm, mayAssumeCond, mayProveCond)
  -- now try to prune if we can translate the things
  result <- case (mayBodyTerm, mayAssumeCond, mayProveCond) of
    -- if everything can be translated, try to prune with it
    (Right _, Right assumeCond, Left _) -> do
      -- liftIO $ putStrLn "prunning with unknown prove..."
      -- _ <- liftIO getLine
      pruneAndValidate (And [Native assumeCond]) Nothing []
    (Right _, Right assumeCond, Right proveCond) -> do
      -- liftIO $ putStrLn "prunning..."
      -- _ <- liftIO getLine
      pruneAndValidate (And [Native assumeCond]) (Just $ And [Native proveCond]) []
    _ -> pure PruneUnknown
  -- step 2. depending on the result, stop or keep going
  case result of
    PruneInconsistentAssumptions -> pure Discharged
    PruneImplicationHolds -> pure Verified
    PruneCounterFound model -> pure $ CounterExample bodyTerm model
    _ -> do
      -- one step of evaluation on each
      -- it is very important that we do all three in parallel,
      -- because otherwise we risk going into a rabbit hole in
      -- one of them, and never learn from the evaluation in other
      -- (for example, expanding a big bodyTerm when the assumeTerm
      -- has a cut-off somewhere)
      (bodyTerm', bodyWasEval) <- prune $ runWriterT (symEvalOneStep bodyTerm)
      (assumeTerm', assummeWasEval) <- prune $ runWriterT (symEvalOneStep assumeTerm)
      (proveTerm', proveWasEval) <- prune $ runWriterT (symEvalOneStep proveTerm)
      -- liftIO $ putStrLn "ONE STEP"
      -- liftIO $ print (pretty bodyTerm')
      -- liftIO $ print (pretty assumeTerm')
      -- liftIO $ print (pretty proveTerm')
      let somethingWasEval = bodyWasEval <> assummeWasEval <> proveWasEval
      -- liftIO $ print somethingWasEval
      -- check the fuel
      noMoreFuel <- gets sestStoppingCondition >>= \s -> s <$> currentStatistics
      -- currentFuel >>= liftIO . print
      if noMoreFuel || somethingWasEval == Any False
        then pure $ CounterExample bodyTerm' (Model [])
        else do
          normBodyTerm <- lift $ normalizeTerm bodyTerm'
          normAssumeTerm <- lift $ normalizeTerm assumeTerm'
          normProveTerm <- lift $ normalizeTerm proveTerm'
          worker resultVar normBodyTerm normAssumeTerm normProveTerm
