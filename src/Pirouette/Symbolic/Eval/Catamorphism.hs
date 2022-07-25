{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Catamorphism where

import Control.Applicative hiding (Const)
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
import qualified PureSMT

data SymEvalSolvers lang = SymEvalSolvers
  { -- | Check whether a path is plausible
    solvePathProblem :: CheckPathProblem lang -> Bool,
    -- | Check whether a certain property currently holds over a given path
    solvePropProblem :: CheckPropertyProblem lang -> PruneResult
  }

data SymEvalEnv lang = SymEvalEnv
  { seeDefs :: PrtOrderedDefs lang,
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
  SymEvalEnv lang ->
  SymTree lang (TermMeta lang SymVar) ->
  [TermMeta lang SymVar]
catamorphism env = concatMap whnfToTerm . cataWHNF def
  where
    -- sharedSolve is here to hint to GHC not to create more than one pool
    -- of SMT solvers, which could happen if sharedSolve were inlined.
    -- TODO: Write a test to check that only one SMT pool is actually created over
    --       multiple calls to runSymEvalWorker.
    {-# NOINLINE sharedSolve #-}
    sharedSolve :: SolverProblem lang res -> res
    sharedSolve = PureSMT.solveOpts (optsPureSMT $ seeOptions env) (mkSolverCtx $ seeDefs env)

    solve :: CheckPathProblem lang -> Bool
    solve = sharedSolve . CheckPath

    -- Cata WHNF will lazily search for the first WHNF of the tree
    cataWHNF ::
      SymEvalSt lang ->
      SymTree lang a ->
      [WHNF lang a]
    cataWHNF st (Cons ci args) = return $ WHNFConstructor ci args
    cataWHNF st (Const c) = return $ WHNFConstant c
    cataWHNF st (Leaf t) = return $ WHNFOther t
    -- TODO: add something to language symeval to decide whether to run this
    -- in call-by-name/value or some mix the user might want.
    -- for now, we're just going on call-by-name:
    cataWHNF st (Call f xs) = cataWHNF st (f xs)
    cataWHNF st (Union trees) = concatMap (cataWHNF st) trees
    cataWHNF st (Dest motif cases) = do
      motif' <- cataWHNF st motif
      case motif' of
        WHNFConstructor ci args -> cataWHNF st (cases (ci, args))
        _ -> error "Type error!"
    cataWHNF st (Learn delta t) =
      case learn delta st of
        Just st' | sestAssignments st' <= maxAssignments (seeOptions env) -> cataWHNF st' t
        _ -> empty
    cataWHNF st (Bin b args) = undefined

    whnfToTerm :: WHNF lang (TermMeta lang SymVar) -> [TermMeta lang SymVar]
    whnfToTerm (WHNFConstructor ci args) = do
      -- TODO: seems like we have to thread state through or re-structure the whole function;
      -- without a 'SymEvalSt' we can't recursively call cataWHNF. In fact, we might have
      -- the need for a synchronization point here anyway; say we have the following WHNF:
      --
      -- > WHNFConstructor "Tuple2"
      -- >   [ { (ca , ra) , (ca', ra') } -- here are SymTrees, written as a set of (Constraint,Res)
      -- >   , { (cb , rb) }
      -- >   ]
      -- > ===>
      -- > { (ca && cb , Tuple2 ca cb) , (ca' && cb , Tuple2 ca' cb) }
      --
      -- CH: Doesn't this suggest the anamorphism should be doing this branching so we
      -- never have to come back up?
      args' <- mapM _ args
      return $ mkConsApp (ciCtorName ci) args'
    whnfToTerm (WHNFConstant t) = return $ mkConstant t
    whnfToTerm (WHNFOther t) = return t

-- return $ fmap (mkConsApp (ciCtorName ci)) args'

learn :: DeltaEnv lang -> SymEvalSt lang -> Maybe (SymEvalSt lang)
learn = undefined

mkConsApp :: Name -> [TermMeta lang SymVar] -> TermMeta lang SymVar
mkConsApp n args = SystF.App (SystF.Free (TermSig n)) $ map SystF.TermArg args

mkConstant :: Constants lang -> TermMeta lang SymVar
mkConstant c = SystF.App (SystF.Free (Constant c)) []

pathDistr :: [Path lang res] -> Path lang [res]
pathDistr = foldl' combineOne emptyPath
  where
    emptyPath :: Path lang [res]
    emptyPath = undefined

    -- mappends things like constraint, etc...
    combineOne :: Path lang [res] -> Path lang res -> Path lang [res]
    combineOne = undefined

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

{-
data L a where
  L :: forall a b . ([b] -> [b]) -> (b -> a) -> L a

toList :: L a -> [a]
toList (L xs f) = map f (xs [])

fromList :: [a] -> L a
fromList xs = L (xs ++) id

singletonL :: a -> L a
singletonL a = L (a:) id

instance Functor L where
  fmap f (L x fs) = L x (f . fs)

-- | Difference lists for efficient concats, but we also want efficient maps,
-- so we'll coyoneda this monster in the actual type we use: 'L'
newtype L0 a = L0 {unL0 :: [a] -> [a]}

singletonL0 :: a -> L0 a
singletonL0 = L0 . (:)

emptyL0 :: L0 a
emptyL0 = L0 id

consL0 :: a -> L0 a -> L0 a
consL0 x xs = L0 $ (x :) . unL0 xs

cat2 :: L0 a -> L0 a -> L0 a
L0 f `cat2` L0 g = L0 (f . g)

concatL0 :: [L0 a] -> L0 a
concatL0 = foldl cat2 emptyL0
-}
