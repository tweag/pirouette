{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Pirouette.Term.Symbolic.Prover where

import Control.Monad.Except
import Control.Monad.Writer
import qualified Pirouette.SMT as SMT
import Pirouette.SMT.Constraints
import Pirouette.SMT.Translation
import Pirouette.Term.Syntax
import Pirouette.Term.Symbolic.Eval
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
data Problem lang
  = Problem {
    problemResultTy :: Type lang,
    problemBody     :: Term lang,
    problemAssume   :: Term lang,
    problemProve    :: Term lang
  } deriving (Eq, Show)

type SymTerm lang = TermMeta lang SymVar

rESULTNAME :: Name
rESULTNAME = "__result"

prove :: (SymEvalConstr lang  m, MonadIO m)
      => Problem lang -> m [Path lang (EvaluationWitness lang)]
prove problem = symevalT InfiniteFuel $ proveRaw problem

proveRaw
  :: forall lang m. SymEvalConstr lang m 
  => Problem lang -> SymEvalT lang m (EvaluationWitness lang)
proveRaw Problem { .. } = do
  -- get types for lambdas
  let (lams, _) = R.getHeadLams problemBody
  -- declare new symbolic variables
  argVars <- declSymVars lams
  [resultVar] <- declSymVars [(rESULTNAME, problemResultTy)]
  let allVars = resultVar : argVars
  -- create the new three terms
  let bodyTerm   = createTerm problemBody argVars
      assumeTerm = createTerm problemAssume allVars
      proveTerm  = createTerm problemProve allVars
  -- now we start the loop
  worker resultVar bodyTerm assumeTerm proveTerm
  where
    createTerm :: Term lang -> [SymVar] -> SymTerm lang
    createTerm body vars =
      R.appN (termToMeta body) $ map (R.TermArg . (`R.App` []) . R.Meta) vars

worker
  :: forall lang m. SymEvalConstr lang m 
  => SymVar -> SymTerm lang -> SymTerm lang -> SymTerm lang
  -> SymEvalT lang m (EvaluationWitness lang)
worker resultVar bodyTerm assumeTerm proveTerm = do
  -- step 1. try to prune the thing
  -- introduce the assumption about the result
  learn $ And [Assign (symVar resultVar) bodyTerm]
  result <- case (runExcept (translateTerm [] assumeTerm), runExcept (translateTerm [] proveTerm)) of
    -- if the assumption and thing-to-prove can be translated, try to prune with it
    (Right assumeCond, Right proveCond) -> do
      -- liftIO $ print (pretty bodyTerm)
      pruneAndValidate (And [Native assumeCond]) (And [Native proveCond]) []
    _ -> pure SMT.Unknown
  -- step 2. depending on the result, stop or keep going
  case result of
    SMT.Unsat -> pure Verified
    SMT.Sat -> pure $ CounterExample bodyTerm
    _ -> do -- one step of evaluation on each
      (bodyTerm', bodyWasEval) <- prune $ runWriterT (symEvalOneStep bodyTerm)
      (assumeTerm', assummeWasEval) <- prune $ runWriterT (symEvalOneStep assumeTerm)
      (proveTerm', proveWasEval) <- prune $ runWriterT (symEvalOneStep proveTerm)
      let somethingWasEval = bodyWasEval <> assummeWasEval <> proveWasEval
      if somethingWasEval == Any False
        then pure $ CounterExample bodyTerm'
        else worker resultVar bodyTerm' assumeTerm' proveTerm'