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

catamorphism ::
  forall lang.
  (LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Options ->
  TermSet lang ->
  [Path lang (TermMeta lang SymVar)]
catamorphism defs opts = map (uncurry path) . concatMap inject . cataWHNF def
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

    inject :: (SymEvalSt lang, (WHNFTermHead lang, [TermSet lang])) -> [(SymEvalSt lang, TermMeta lang SymVar)]
    inject (st, (hd, args)) =
      let worlds = map (concatMap inject . cataWHNF st) args
       in flip map worlds $ \xs ->
            let (sts, args') = unzip xs
             in (if null sts then st else mconcat sts, buildTerm hd args')

    buildTerm :: WHNFTermHead lang -> [TermMeta lang SymVar] -> TermMeta lang SymVar
    buildTerm (WHNFCotr (ConstructorInfo _ n _)) args = SystF.App (SystF.Free $ TermSig n) (map SystF.TermArg args)
    buildTerm _ _ = error "not yet implemented"

    cataWHNF ::
      SymEvalSt lang ->
      TermSet lang ->
      [(SymEvalSt lang, (WHNFTermHead lang, [TermSet lang]))]
    cataWHNF st (TermSet t) = concatMap (uncurry cataSpine) $ cataTree st t

    cataTree ::
      SymEvalSt lang ->
      Tree (DeltaEnv lang) (Spine lang (TermSet lang)) ->
      [(SymEvalSt lang, Spine lang (TermSet lang))]
    cataTree st (Leaf spine) = return (st, spine)
    cataTree st (Union worlds) = concatMap (cataTree st) worlds
    cataTree st (Learn delta t) =
      case learn delta st of
        Just st'
          | sestAssignments st' <= maxAssignments opts -> cataTree st' t
        _ -> empty

    cataSpine ::
      SymEvalSt lang ->
      Spine lang (TermSet lang) ->
      [(SymEvalSt lang, (WHNFTermHead lang, [TermSet lang]))]
    cataSpine s0 (Next x) =
      concatMap (uncurry cataSpine) (cataTree s0 $ unTermSet x)
    cataSpine s0 (Dest worlds motive) = do
      (s1, (hd, args)) <- cataSpine s0 motive
      case hd of
        WHNFCotr ci -> cataSpine s1 (worlds (ci, map Next args))
        _ -> error "Type error: destructing something that is not a constructor!"
    -- TODO: add something to LanguageSymEval to do call by value. See
    -- issues #137 and #138 for more
    cataSpine s0 (Call _n f args) = cataSpine s0 (f args)
    cataSpine s0 (Head hd args) = return (s0, (hd, map (TermSet . pure) args))

{-
    cataWHNF ::
      SymEvalSt lang ->
      Spine lang (TermMeta lang SymVar) ->
      [(SymEvalSt lang, (WHNFTermHead lang, [Spine lang (TermMeta lang SymVar)]))]
    cataWHNF s0 (Next x) =
      concatMap (uncurry cataWHNF) (cataTree s0 x)
    cataWHNF s0 (Dest worlds motive) = do
      (s1, (hd, args)) <- cataWHNF s0 _
      case hd of
        WHNFCotr ci -> cataWHNF s1 (worlds (ci, args))
        _ -> error "Type error: destructing something that is not a constructor!"
    cataWHNF _ _ = undefined
-}

{-

    -- Cata WHNF will lazily search for the first WHNF of the tree
    cataWHNF ::
      SymEvalSt lang ->
      SymTree lang SymVar (TermMeta lang SymVar) ->
      [(SymEvalSt lang, WHNF lang (TermMeta lang SymVar))]
    cataWHNF st (Leaf t) = return (st, WHNFOther t)
    cataWHNF st (Call hd f xs) =
      case hd of
        CallSig _ -> cataWHNF st (f xs)
        CallBuiltin _ -> undefined
        CallCotr ci -> return (st, WHNFConstructor ci xs)
    cataWHNF st (Union trees) = concatMap (cataWHNF st) trees
    cataWHNF st (Dest cases motif) = do
      (st', motif') <- cataWHNF st motif
      case motif' of
        WHNFConstructor ci args -> cataWHNF st' (cases (ci, args))
        _ -> error "Type error!"
    cataWHNF st (Learn delta t) =
    -- Let's not worry about builtins at all right now. With plain inductive types
    -- we can already do so much to check whether this monster is going to work before
    -- refining the interface to evaluating builtins in LanguageSymEval

    whnfToTerm :: SymEvalSt lang -> WHNF lang (TermMeta lang SymVar) -> [(SymEvalSt lang, TermMeta lang SymVar)]
    whnfToTerm st (WHNFConstructor ci args) =
      let args' = traverse (cata st) args
       in flip map args' $ \xs ->
            (if null xs then const st else mconcat) *** mkConsApp (ciCtorName ci) $
              unzip xs
    -- return $ mkConsApp (ciCtorName ci) args'
    whnfToTerm st (WHNFOther t) = return (st, t)
-}
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
