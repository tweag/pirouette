{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Catamorphism where

import Control.Applicative hiding (Const)
import Control.Arrow ((***))
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

data WHNF lang a
  = WHNFConstructor ConstructorInfo [SymTree lang a]
  | WHNFConstant (Constants lang)
  | WHNFOther a

catamorphism ::
  forall lang.
  (LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Options ->
  SymTree lang (TermMeta lang SymVar) ->
  [Path lang (TermMeta lang SymVar)]
catamorphism defs opts = map (uncurry path) . cata def
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

    cata ::
      SymEvalSt lang ->
      SymTree lang (TermMeta lang SymVar) ->
      [(SymEvalSt lang, TermMeta lang SymVar)]
    cata st = concatMap (uncurry whnfToTerm) . cataWHNF st

    -- Cata WHNF will lazily search for the first WHNF of the tree
    cataWHNF ::
      SymEvalSt lang ->
      SymTree lang a ->
      [(SymEvalSt lang, WHNF lang a)]
    cataWHNF st (Cons ci args) = return (st, WHNFConstructor ci args)
    cataWHNF st (Const c) = return (st, WHNFConstant c)
    cataWHNF st (Leaf t) = return (st, WHNFOther t)
    -- TODO: add something to language symeval to decide whether to run this
    -- in call-by-name/value or some mix the user might want.
    -- for now, we're just going on call-by-name:
    cataWHNF st (Call f xs) = cataWHNF st (f xs)
    cataWHNF st (Union trees) = concatMap (cataWHNF st) trees
    cataWHNF st (Dest motif cases) = do
      (st', motif') <- cataWHNF st motif
      case motif' of
        WHNFConstructor ci args -> cataWHNF st' (cases (ci, args))
        _ -> error "Type error!"
    cataWHNF st (Learn delta t) =
      case learn delta st of
        Just st'
          | sestAssignments st' <= maxAssignments opts -> cataWHNF st' t
        _ -> empty
    -- Let's not worry about builtins at all right now. With plain inductive types
    -- we can already do so much to check whether this monster is going to work before
    -- refining the interface to evaluating builtins in LanguageSymEval
    cataWHNF st (Bin b args) = return (st, WHNFOther undefined)

    whnfToTerm :: SymEvalSt lang -> WHNF lang (TermMeta lang SymVar) -> [(SymEvalSt lang, TermMeta lang SymVar)]
    whnfToTerm st (WHNFConstructor ci args) =
      let args' = traverse (cata st) args
          ctor = mkConsApp (ciCtorName ci)
       in flip map args' $ \xs ->
            (if null xs then const st else mconcat) *** mkConsApp (ciCtorName ci) $
              unzip xs
    -- return $ mkConsApp (ciCtorName ci) args'
    whnfToTerm st (WHNFConstant t) = return (st, mkConstant t)
    whnfToTerm st (WHNFOther t) = return (st, t)

-- return $ fmap (mkConsApp (ciCtorName ci)) args'

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
