{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Symbolic.Prover where

import Control.Monad.Reader
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
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
prove opts problem = symeval opts $ proveRaw problem

-- | Prove without any stopping condition.
proveUnbounded ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  Options ->
  Problem lang ->
  m [Path lang (EvaluationWitness lang)]
proveUnbounded opts = prove (opts {shouldStop = const False})

-- | Executes the problem while the stopping condition is valid until
--  the supplied predicate returns @True@. A return value of @Nothing@
--  means that on all paths that we looked at they were either verified or
--  they reached the stopping condition.
proveAny ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  Options ->
  (Path lang (EvaluationWitness lang) -> Bool) ->
  Problem lang ->
  m (Maybe (Path lang (EvaluationWitness lang)))
proveAny opts p problem = fst <$> proveAnyAccum opts p problem

proveAnyAccum ::
  (SymEvalConstr lang, PirouetteDepOrder lang m) =>
  Options ->
  (Path lang (EvaluationWitness lang) -> Bool) ->
  Problem lang ->
  m (Maybe (Path lang (EvaluationWitness lang)), PathStatistics)
proveAnyAccum opts p problem = symevalAnyPathAccum countPath ps0 opts p $ proveRaw problem

data PathStatistics = PathStatistics
  { numDischarged :: Integer,
    numVerified :: Integer
  }
  deriving (Eq, Show)

countPath :: Path lang (EvaluationWitness lang) -> PathStatistics -> PathStatistics
countPath p s0 = case pathResult p of
  Verified -> s0 {numVerified = numVerified s0 + 1}
  Discharged -> s0 {numDischarged = numDischarged s0 + 1}
  _ -> s0

ps0 :: PathStatistics
ps0 = PathStatistics 0 0

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
  -- | The symbolic variable holding the current result
  SymVar ->
  -- | The body that is being symbolically evaluated
  SymTerm lang ->
  -- | The antecedent, which is a term of type Bool in @lang@, whatever that may be
  SymTerm lang ->
  -- | The consequent, also of type Bool in @lang@
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
  -- ISSUE!! In PlutusIR, if we don't want to have builtin booleans because of the plutus
  -- compiler being annoying with them, we can't just 'translate proveTerm', for instance,
  -- since it might be @App (Free (TermSig "False")) []@, which will translate
  -- to @(as pir_False pir_Bool)@ which is NOT a boolean. I think that maybe giving language
  -- implementors the chance to translate that term to native SMT true and falses
  -- through translateTerm might be nice!
  -- step 1. try to prune the thing
  mayBodyTerm <- translate bodyTerm
  mayAssumeCond <- fmap (isTrue @lang) <$> translate assumeTerm
  mayProveCond <- fmap (isTrue @lang) <$> translate proveTerm
  -- introduce the assumption about the result, if useful
  case mayBodyTerm of
    Right _ -> learn [resultVar =:= bodyTerm]
    _ -> pure ()
  -- debugPrint $ pretty (mayBodyTerm, mayAssumeCond, mayProveCond)
  -- now try to prune if we can translate the things
  result <- case (mayBodyTerm, mayAssumeCond, mayProveCond) of
    -- if everything can be translated, try to prune with it
    (Right _, Right assumeCond, Left _) -> do
      -- debugPutStr "prunning with unknown prove..."
      -- _ <- liftIO getLine
      pruneAndValidate assumeCond Nothing []
    (Right _, Right assumeCond, Right proveCond) -> do
      -- debugPutStr "prunning..."
      -- _ <- liftIO getLine
      pruneAndValidate assumeCond (Just proveCond) []
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
      noMoreFuel <- asks (shouldStop . seeOptions) >>= \s -> s <$> currentStatistics
      -- currentFuel >>= liftIO . print
      if noMoreFuel || somethingWasEval == Any False
        then pure $ CounterExample bodyTerm' (Model [])
        else do
          worker resultVar bodyTerm' assumeTerm' proveTerm'
