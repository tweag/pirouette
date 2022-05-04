{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.Symbolic.Prover where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Pirouette.Monad (termIsWHNFOrMeta)
import Pirouette.SMT.Base (LanguageSMT (isStuckBuiltin))
import Pirouette.SMT.Constraints
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
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
prove problem = symevalT InfiniteFuel $ proveRaw problem

proveWithFuel ::
  (SymEvalConstr lang m, MonadIO m) =>
  Int ->
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
proveWithFuel f problem = symevalT (Fuel f) $ proveRaw problem

proveAny ::
  (SymEvalConstr lang m, MonadIO m) =>
  (Path lang (EvaluationWitness lang) -> Bool) ->
  Problem lang ->
  m Bool
proveAny p problem = symevalAnyPath p InfiniteFuel $ proveRaw problem

proveAnyWithFuel ::
  (SymEvalConstr lang m, MonadIO m) =>
  Int ->
  (Path lang (EvaluationWitness lang) -> Bool) ->
  Problem lang ->
  m Bool
proveAnyWithFuel f p problem = symevalAnyPath p (Fuel f) $ proveRaw problem

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
  -- liftIO $ putStrLn "ONE STEP"
  -- liftIO $ print (pretty bodyTerm)
  -- liftIO $ print (pretty assumeTerm)
  -- liftIO $ print (pretty proveTerm)
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
  -- now try to prune if we can translate the things
  result <- case (mayBodyTerm, mayAssumeCond, mayProveCond) of
    -- if everything can be translated, try to prune with it
    (Right _, Right assumeCond, Right proveCond) -> do
      -- liftIO $ putStrLn "prunning..."
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
      -- liftIO $ putStrLn "ONE STEP"
      -- liftIO $ print (pretty bodyTerm')
      -- liftIO $ print (pretty assumeTerm')
      -- liftIO $ print (pretty proveTerm')
      let somethingWasEval = bodyWasEval <> assummeWasEval <> proveWasEval
      -- liftIO $ print somethingWasEval
      -- check the fuel
      noMoreFuel <- fuelExhausted <$> currentFuel
      -- currentFuel >>= liftIO . print
      if noMoreFuel || somethingWasEval == Any False
        then pure $ CounterExample bodyTerm' (Model [])
        else do
          normBodyTerm <- lift $ normalizeTerm bodyTerm'
          normAssumeTerm <- lift $ normalizeTerm assumeTerm'
          normProveTerm <- lift $ normalizeTerm proveTerm'
          worker resultVar normBodyTerm normAssumeTerm normProveTerm
