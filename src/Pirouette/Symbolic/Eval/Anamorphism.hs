{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Symbolic.Eval.Anamorphism where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Parallel.Strategies
import Data.Foldable
import Data.List (genericLength)
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import ListT.Weighted (WeightedList)
import qualified ListT.Weighted as ListT
import Pirouette.Monad
import Pirouette.Monad.Maybe
import qualified Pirouette.SMT.Constraints as C
import qualified Pirouette.SMT.FromTerm as Tr
import qualified Pirouette.SMT.Monadic as SMT
import Pirouette.Symbolic.Eval.SMT
import Pirouette.Symbolic.Eval.Types as X
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import qualified PureSMT
import Supply

-- | A 'Tree' which denotes a set of pairs of @(monoid, leaf)@
data Tree monoid leaf
  = Empty
  | Leaf leaf
  | Learn monoid (Tree monoid leaf)
  | Union [Tree monoid leaf]
  | forall a. Call ([Tree monoid a] -> Tree monoid leaf) [Tree monoid a]

instance Functor (Tree m) where
  fmap _ Empty = Empty
  fmap f (Learn str t) = Learn str $ fmap f t
  fmap f (Leaf x) = Leaf $ f x
  fmap f (Call ts as) = Call (fmap f . ts) as
  fmap f (Union ts) = Union $ map (fmap f) ts

instance Applicative (Tree m) where
  pure = Leaf
  (<*>) = ap

instance Alternative (Tree m) where
  empty = Empty

  Empty <|> u = u
  t <|> Empty = t
  Union t <|> Union u = Union (t ++ u)
  Union t <|> u = Union (u : t)
  t <|> Union u = Union (t : u)
  t <|> u = Union [t, u]

instance Monad (Tree m) where
  Empty >>= _ = Empty
  Leaf x >>= f = f x
  Learn str t >>= f = Learn str (t >>= f)
  Call body args >>= f = Call (f <=< body) args
  Union ts >>= f = Union $ map (>>= f) ts

treeDistr :: (Traversable t) => t (Tree m a) -> Tree m (t a)
treeDistr = sequenceA

data Env lang = Env
  { envSymVars :: [(SymVar, Type lang)],
    envConstraint :: [Constraint lang]
  }

ana ::
  (Pretty meta, LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Supply Name ->
  TermMeta lang meta ->
  Tree (Env lang) (TermMeta lang meta)
ana defs s t@(hd `SystF.App` args) =
  case hd of
    SystF.Free (Builtin bin) ->
      _
    SystF.Free (TermSig n) ->
      case prtDefOf TermNamespace n `runReader` defs of
        DTypeDef _ -> error "Can't evaluate typedefs"
        DConstructor _ _ -> justEvaluateArgs
        DDestructor tyName -> anaDestructor defs s (unsafeUnDest t `runReader` defs)
        DFunction _ body _ ->
          _
    SystF.Meta vr -> do
      _

    -- in any other case, don't try too hard
    _ -> justEvaluateArgs
  where
    justEvaluateArgs = undefined
ana _ _ t@SystF.Lam {} =
  -- Note that our AST only represents terms in normal form, hence
  -- > App (Lam ...) ...
  -- Never appears, so beta-reduction does not enter the game here.
  -- We could try going into the lambda an evaluating its body
  -- considering its variable to be symbolic, but this seems to win us
  -- nothing. For example, if we are evaluating:
  -- > map (\x -> x + 1) l
  -- then going into (\x -> x + 1) would only lead to reconstructing it,
  -- the real evaluation work happens on the definition of 'map'.
  -- We have decided to *not* go under lambdas.
  pure t
ana _ _ t@SystF.Abs {} =
  error $
    unlines
      [ "Can't symbolically evaluate polymorphic terms",
        "Did you not monomorphize/defunctionalize before?",
        "term: " ++ renderSingleLineStr (pretty t)
      ]

anaDestructor ::
  (Pretty meta, LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Supply Name ->
  UnDestMeta lang meta ->
  Tree (Env lang) (TermMeta lang meta)
anaDestructor defs s (UnDestMeta _ tyName tyParams motive tyRes cases excess) =
  let (Datatype _ _ _ consList) = prtTypeDefOf tyName `runReader` defs
      tMotive = ana defs s motive
   in Union $
        for2 consList cases $ \(consName, constTy) -> do
          _

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 as bs f = zipWith f as bs
