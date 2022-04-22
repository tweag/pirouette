{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.Symbolic.Prover where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Pirouette.SMT.Constraints
import Pirouette.SMT.Translation
import Pirouette.Term.Symbolic.Eval
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Pirouette.Monad (termIsWHNFOrMeta, termIsBuiltin)

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
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
prove problem = symevalT InfiniteFuel $ proveRaw problem

proveWithFuel ::
  (SymEvalConstr lang m, MonadIO m) =>
  Int ->
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
proveWithFuel f problem = symevalT (Fuel f) $ proveRaw problem

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
  worker resultVar bodyTerm assumeTerm proveTerm
  where
    createTerm :: Term lang -> [SymVar] -> SymTerm lang
    createTerm body vars =
      R.appN (termToMeta body) $ map (R.TermArg . (`R.App` []) . R.Meta) vars

worker ::
  forall lang m.
  SymEvalConstr lang m =>
  SymVar ->
  SymTerm lang ->
  SymTerm lang ->
  SymTerm lang ->
  SymEvalT lang m (EvaluationWitness lang)
worker resultVar bodyTerm assumeTerm proveTerm = do
  knownNames <- gets sestKnownNames
  -- liftIO $ print (pretty bodyTerm)
  -- liftIO $ print (pretty assumeTerm)
  -- liftIO $ print (pretty proveTerm)
  -- _ <- liftIO getLine
  -- step 1. try to prune the thing
  -- introduce the assumption about the result, if useful
  mayBodyTerm <- runTranslator $ translateTerm knownNames Nothing bodyTerm
  case mayBodyTerm of
    Right _ -> learn $ And [Assign (symVar resultVar) bodyTerm]
    _ -> pure ()
  -- now try to prune if we can translate the things
  whnfBody <- termIsWHNFOrMeta bodyTerm
  mayAssumeCond <- runTranslator $ translateTerm knownNames Nothing assumeTerm
  mayProveCond <- runTranslator $ translateTerm knownNames Nothing proveTerm
  result <- case (mayBodyTerm, mayAssumeCond, mayProveCond) of
    -- if everything can be translated, try to prune with it
    (Right _, Right (assumeCond, _), Right (proveCond, _))
      | whnfBody || termIsBuiltin bodyTerm -> do
      pruneAndValidate (And [Native assumeCond]) (And [Native proveCond]) []
    _ -> pure PruneUnknown
  -- step 2. depending on the result, stop or keep going
  case result of
    PruneInconsistentAssumptions -> pure Discharged
    PruneImplicationHolds -> pure Verified
    PruneCounterFound model -> pure $ CounterExample bodyTerm model
    _ -> do
      -- one step of evaluation on each
      (bodyTerm', bodyWasEval) <- prune $ runWriterT (symEvalOneStep bodyTerm)
      (assumeTerm', assummeWasEval) <- prune $ runWriterT (symEvalOneStep assumeTerm)
      (proveTerm', proveWasEval) <- prune $ runWriterT (symEvalOneStep proveTerm)
      let somethingWasEval = bodyWasEval <> assummeWasEval <> proveWasEval
      noMoreFuel <- fuelExhausted <$> currentFuel
      if noMoreFuel || somethingWasEval == Any False
        then pure $ CounterExample bodyTerm' []
        else do
          normBodyTerm <- lift $ normalizeTerm bodyTerm'
          normAssumeTerm <- lift $ normalizeTerm assumeTerm'
          normProveTerm <- lift $ normalizeTerm proveTerm'
          worker resultVar normBodyTerm normAssumeTerm normProveTerm
