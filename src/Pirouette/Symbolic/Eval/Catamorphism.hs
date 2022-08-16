{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Catamorphism where

import Control.Applicative hiding (Const)
import Control.Arrow (Arrow (first), (***))
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Parallel.Strategies
import Data.Default
import Data.Foldable hiding (toList)
import Data.List (genericLength)
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import Debug.Trace
import ListT.Weighted (WeightedList)
import qualified ListT.Weighted as ListT
import Pirouette.Monad hiding (WHNFResult (..))
import Pirouette.Monad.Maybe
import qualified Pirouette.SMT.Constraints as C
import qualified Pirouette.SMT.FromTerm as Tr
import qualified Pirouette.SMT.Monadic as SMT
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
  [Path lang WHNFTerm]
catamorphism defs opts = map (uncurry path) . go def
  where
    orderedDefs = elimEvenOddMutRec defs

    -- sharedSolve is here to hint to GHC not to create more than one pool
    -- of SMT solvers, which could happen if sharedSolve were inlined.
    -- TODO: Write a test to check that only one SMT pool is actually created over
    --       multiple calls to runSymEvalWorker.
    {-# NOINLINE sharedSolve #-}
    sharedSolve :: SolverProblem lang res -> res
    sharedSolve = PureSMT.solveOpts (optsPureSMT opts) (mkSolverCtx orderedDefs)

    solve :: CheckPathProblem lang -> Bool
    solve = sharedSolve . CheckPath

    go :: SymEvalSt lang -> TermSet lang -> [(SymEvalSt lang, WHNFTerm)]
    go st ts = do
      (st', res) <- goWHNF st ts
      case res of
        Left m -> return (st', WHNFMeta m)
        Right WHNFBottom -> return (st', WHNFLayer WHNFBottom)
        Right (WHNFCotr ci ts') -> do
          (sts, args) <- combineArgs st' <$> traverse (go st') ts'
          return (sts, WHNFLayer (WHNFCotr ci args))

    goWHNF :: SymEvalSt lang -> TermSet lang -> [(SymEvalSt lang, Either SymVar (WHNFLayer (TermSet lang)))]
    goWHNF st (Union tss) = tss >>= goWHNF st
    goWHNF st (Inst m Nothing) = return (st, Left m)
    goWHNF st (Inst m (Just ts)) = goWHNF st ts
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
    goWHNF st (Spine t) = return (st, Right t)

    combineArgs :: (Monoid s) => s -> [(s, a)] -> (s, [a])
    combineArgs s0 [] = (s0, [])
    combineArgs _ xs = first mconcat . unzip $ xs

learn :: DeltaEnv lang -> SymEvalSt lang -> Maybe (SymEvalSt lang)
learn (DeclSymVars vs) st = Just $ st {sestGamma = sestGamma st `union` M.mapKeys symVar vs}
  where
    union = M.unionWithKey (\k _ _ -> error $ "Key already declared: " ++ show k)
learn (Assign v t) st =
  Just $
    st
      { sestConstraint = c <> sestConstraint st,
        sestAssignments = sestAssignments st + 1
      }
  where
    c = SMT.And [SMT.Assign v t]

mkConsApp :: Name -> [TermMeta lang SymVar] -> TermMeta lang SymVar
mkConsApp n args = SystF.App (SystF.Free (TermSig n)) $ map SystF.TermArg args

mkConstant :: Constants lang -> TermMeta lang SymVar
mkConstant c = SystF.App (SystF.Free (Constant c)) []

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
