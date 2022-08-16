{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Catamorphism where

import Control.Applicative hiding (Const)
import Control.Arrow (first)
import Control.Monad.Reader
import Control.Parallel.Strategies
import Data.Default
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import Debug.Trace
import Pirouette.Monad hiding (WHNFResult (..))
import qualified Pirouette.SMT.Monadic as SMT
import Pirouette.Symbolic.Eval.Constraints
import Pirouette.Symbolic.Eval.SMT
import Pirouette.Symbolic.Eval.Types as X
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations
import qualified PureSMT

data SymEvalSolvers lang = SymEvalSolvers
  { -- | Check whether a path is plausible
    solvePathProblem :: CheckPathProblem lang -> Bool,
    -- | Check whether a certain property currently holds over a given path
    solvePropProblem :: CheckPropertyProblem lang -> PruneResult
  }

data SymEvalEnv lang = SymEvalEnv
  { seeDefs :: PrtUnorderedDefs lang,
    seeSolvers :: SymEvalSolvers lang,
    seeOptions :: Options
  }

catamorphism ::
  forall lang.
  (LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Options ->
  TermSet lang ->
  [Path lang (WHNFTerm lang)]
catamorphism defs opts = map (uncurry path) . go def
  where
    orderedDefs = elimEvenOddMutRec defs

    -- sharedSolve is here to hint to GHC not to create more than one pool
    -- of SMT solvers, which could happen if sharedSolve were inlined.
    -- TODO: Write a test to check that only one SMT pool is actually created over
    --       multiple calls to catamorphism.
    {-# NOINLINE sharedSolve #-}
    sharedSolve :: SolverProblem lang res -> res
    sharedSolve = PureSMT.solveOpts (optsPureSMT opts) (mkSolverCtx orderedDefs)

    solve :: CheckPathProblem lang -> Bool
    solve = sharedSolve . CheckPath

    go :: SymEvalSt lang -> TermSet lang -> [(SymEvalSt lang, WHNFTerm lang)]
    go st ts = do
      (st', res) <- goWHNF st ts
      case res of
        Left m -> return (st', WHNFMeta m)
        Right WHNFBottom -> return (st', WHNFLayer WHNFBottom)
        Right (WHNFConst c) -> return (st', WHNFLayer $ WHNFConst c)
        Right (WHNFBuiltin bin ts') -> do
          (sts, args) <- combineArgs st' <$> traverse (go st') ts'
          trace
            ( "Branches bin term: " ++ show bin ++ "\n"
                ++ unlines
                  (map (renderSingleLineStr . pretty) args)
            )
            (return ())
          case branchesBuiltinTerm bin args `runReader` defs of
            Nothing -> []
            Just res' -> do
              (ds, t) <- res'
              case learnN ds sts of
                Nothing -> empty
                Just sts' -> return (sts', t)
        Right (WHNFCotr ci ts') -> do
          (sts, args) <- combineArgs st' <$> traverse (go st') ts'
          return (sts, WHNFLayer (WHNFCotr ci args))

    goWHNF :: SymEvalSt lang -> TermSet lang -> [(SymEvalSt lang, Either SymVar (WHNFLayer lang (TermSet lang)))]
    goWHNF st (Union tss) = concatMap (goWHNF st) tss
    goWHNF st (Inst m Nothing) = return (st, Left m)
    goWHNF st (Inst _ (Just ts)) = goWHNF st ts
    goWHNF st (Learn delta ts) =
      case learn delta st of
        Just st' | sestAssignments st' < maxAssignments opts -> goWHNF st' ts
        _ -> empty
    goWHNF st (Call _ f args) = goWHNF st (f args)
    goWHNF st (Dest f x) = do
      (st', res) <- goWHNF st x
      case res of
        Left _ -> empty -- can't match on meta
        Right WHNFBottom -> return (st', Right WHNFBottom) -- matching on bottom is bottom
        Right (WHNFCotr ci ts') -> goWHNF st' (f (ci, ts'))
        Right (WHNFConst _) -> error "Type error: motive of match can't be const"
        Right (WHNFBuiltin _ _) -> error "Type error: motive of match can't be builtin"
    goWHNF st (Spine t) = return (st, Right t)

    combineArgs :: (Monoid s) => s -> [(s, a)] -> (s, [a])
    combineArgs s0 [] = (s0, [])
    combineArgs _ xs = first mconcat . unzip $ xs

learnN :: (Language lang) => [DeltaEnv lang] -> SymEvalSt lang -> Maybe (SymEvalSt lang)
learnN [] s = return s
learnN (d : ds) s = learn d s >>= learnN ds

learn :: (Language lang) => DeltaEnv lang -> SymEvalSt lang -> Maybe (SymEvalSt lang)
learn (DeclSymVars vs) st = Just $ st {sestGamma = sestGamma st `union` M.mapKeys symVar vs}
  where
    union = M.unionWithKey (\k _ _ -> error $ "Key already declared: " ++ show k)
learn (Assign v t) st =
  case unifyMetaWith (sestConstraint st) v t of
    Nothing -> Nothing
    Just cs' ->
      Just $
        st
          { sestConstraint = cs',
            sestAssignments = sestAssignments st + 1
          }

-- * Auxiliar Defs

mkSolverCtx :: (SMT.LanguageSMT lang) => PrtOrderedDefs lang -> SolverSharedCtx lang
mkSolverCtx defs =
  let decls = prtDecls defs
      dependencyOrder = prtDepOrder defs
      definedTypes = mapMaybe (R.argElim (lkupTypeDefOf decls) (const Nothing)) dependencyOrder
      allFns = mapMaybe (R.argElim (const Nothing) (lkupFunDefOf decls)) dependencyOrder
      fns = mapMaybe (\(n, fd) -> (n,) <$> SMT.supportedUninterpretedFunction fd) allFns
   in SolverSharedCtx definedTypes fns
  where
    lkupTypeDefOf decls name = case M.lookup (TypeNamespace, name) decls of
      Just (DTypeDef tdef) -> Just (name, tdef)
      _ -> Nothing

    lkupFunDefOf decls name = case M.lookup (TermNamespace, name) decls of
      Just (DFunDef fdef) -> Just (name, fdef)
      _ -> Nothing

-- TODO: instead of lists, we can rely on the impredicative encoding of lists:
-- > type List a = forall r. (a -> r -> r) -> r -> r
