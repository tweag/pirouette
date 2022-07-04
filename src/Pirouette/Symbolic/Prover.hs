{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Symbolic.Prover where

import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Text as T
import Debug.Trace
import Pirouette.Monad (PirouetteDepOrder, termIsWHNFOrMeta)
import Pirouette.SMT.Base (LanguageSMT (isStuckBuiltin))
import Pirouette.SMT.Constraints
import Pirouette.SMT.FromTerm
import Pirouette.Symbolic.Eval
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import Prettyprinter hiding (Pretty, pretty)
import PureSMT (SExpr (..))

-- | A problem represents a triple that should be checked.
-- It should be the case that assuming 'problemAssume',
-- the execution of 'problemBody' always leaves us in a
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

data EvaluationWitness lang
  = Verified
  | Discharged
  | CounterExample (TermMeta lang SymVar) Model
  deriving (Eq, Show)

instance LanguagePretty lang => Pretty (EvaluationWitness lang) where
  pretty Verified = "Verified"
  pretty Discharged = "Discharged"
  pretty (CounterExample t model) =
    vsep
      [ "COUNTER-EXAMPLE",
        "Result:" <+> pretty t,
        "Model:" <+> pretty model
      ]

type SymTerm lang = TermMeta lang SymVar

rESULTNAME :: Name
rESULTNAME = "__result"

-- | Executes the problem returning /all/ paths (up to some stopping condition).
prove ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  Options ->
  StoppingCondition ->
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
prove opts shouldStop problem = symeval opts shouldStop $ proveRaw problem

-- | Prove without any stopping condition.
proveUnbounded ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  Options ->
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
proveUnbounded opts = prove opts (const False)

-- | Executes the problem while the stopping condition is valid until
--  the supplied predicate returns @True@. A return value of @Nothing@
--  means that on all paths that we looked at they were either verified or
--  they reached the stopping condition.
proveAny ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  Options ->
  StoppingCondition ->
  (Path lang (EvaluationWitness lang) -> Bool) ->
  Problem lang ->
  m (Maybe (Path lang (EvaluationWitness lang)))
proveAny opts shouldStop p problem = symevalAnyPath opts shouldStop p $ proveRaw problem

proveRaw ::
  forall lang.
  SymEvalConstr lang =>
  Problem lang ->
  SymEval lang (EvaluationWitness lang)
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

debugPutStr :: String -> SymEval lang ()
debugPutStr = traceM

debugPrint :: (Show a) => a -> SymEval lang ()
debugPrint = traceShowM

worker ::
  forall lang.
  SymEvalConstr lang =>
  SymVar ->
  SymTerm lang ->
  SymTerm lang ->
  SymTerm lang ->
  SymEval lang (EvaluationWitness lang)
worker resultVar bodyTerm assumeTerm proveTerm = do
  -- debugPutStr "ONE STEP"
  -- debugPrint (pretty bodyTerm)
  -- debugPrint (pretty assumeTerm)
  -- debugPrint (pretty proveTerm)
  -- gets sestConstraint >>= debugPrint . pretty
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
  -- debugPrint $ pretty (mayBodyTerm, mayAssumeCond, mayProveCond)
  -- now try to prune if we can translate the things
  result <- case (mayBodyTerm, mayAssumeCond, mayProveCond) of
    -- if everything can be translated, try to prune with it
    (Right _, Right assumeCond, Left _) -> do
      -- debugPutStr "prunning with unknown prove..."
      -- _ <- liftIO getLine
      pruneAndValidate (And [Native assumeCond]) Nothing []
    (Right _, Right assumeCond, Right proveCond) -> do
      -- debugPutStr "prunning..."
      -- _ <- liftIO getLine
      pruneAndValidate (And [Native assumeCond]) (Just $ And [Native proveCond]) []
    _ -> pure PruneUnknown
  -- step 2. depending on the result, stop or keep going
  case result of
    PruneInconsistentAssumptions -> pure Discharged
    PruneImplicationHolds -> pure Verified
    PruneCounterFound model -> pure $ CounterExample bodyTerm model
    _ -> do
      -- one step of evaluation on each,
      -- but going into matches first
      ([bodyTerm', assumeTerm', proveTerm'], somethingWasEval) <-
        prune $
          symEvalParallel [bodyTerm, assumeTerm, proveTerm]
      -- debugPutStr "ONE STEP"
      -- debugPrint (pretty bodyTerm')
      -- debugPrint (pretty assumeTerm')
      -- debugPrint (pretty proveTerm')
      -- debugPrint somethingWasEval
      -- check the fuel
      noMoreFuel <- gets sestStoppingCondition >>= \s -> s <$> currentStatistics
      -- currentFuel >>= liftIO . print
      if noMoreFuel || somethingWasEval == Any False
        then pure $ CounterExample bodyTerm' (Model [])
        else do
          worker resultVar bodyTerm' assumeTerm' proveTerm'
