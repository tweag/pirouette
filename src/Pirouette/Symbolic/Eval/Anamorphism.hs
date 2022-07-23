{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Anamorphism where

import Control.Applicative
import Control.Arrow (second)
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
import Pirouette.Term.Syntax.Subst (shift)
import qualified Pirouette.Term.Syntax.SystemF as SystF
import qualified PureSMT
import Supply

-- | A 'Tree' which denotes a set of pairs of @(monoid, leaf)@
data Tree monoid b
  = Empty
  | Leaf b
  | Learn monoid (Tree monoid b)
  | Union [Tree monoid b]
  | -- | A function call, in an untyped setting, can be seen as something
    -- that takes a list of terms and returns a term (in fact, that's the type of
    -- the partially applied 'SystF.App' constructor!).
    --
    -- > [Term lang] -> Term lang
    --
    -- The trick here consists in lifting those functions to trees:
    --
    -- > [Tree (Term lang)] -> Tree (Term lang)
    --
    -- Finally, because we want a monadic structure, we'll go polymorphic:
    forall a. Call ([Tree monoid a] -> Tree monoid b) [Tree monoid a]
  | -- | Destructors are also a little tricky, because in reality, we need to
    -- consume the motive until /at least/ the first constructor is found, that
    -- is the only guaranteed way to make any progress.
    forall a. Dest (Tree monoid a) ((ConstructorInfo, [Tree monoid a]) -> Tree monoid b)

instance Show (Tree monoid a) where
  show _ = "Tree"

data ConstructorInfo = ConstructorInfo TyName Int

instance Functor (Tree m) where
  fmap _ Empty = Empty
  fmap f (Learn str t) = Learn str $ fmap f t
  fmap f (Leaf x) = Leaf $ f x
  fmap f (Call ts as) = Call (fmap f . ts) as
  fmap f (Dest motive worlds) = Dest motive (fmap f . worlds)
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
  Dest motive worlds >>= f = Dest motive (f <=< worlds)
  Union ts >>= f = Union $ map (>>= f) ts

treeDistr :: (Traversable t) => t (Tree m a) -> Tree m (t a)
treeDistr = sequenceA

data Env lang = Env
  { envSymVars :: [(SymVar, Type lang)],
    envConstraint :: [Constraint lang]
  }

data DeltaEnv lang
  = DeclSymVars [(SymVar, Type lang)]
  | Unify (TermMeta lang SymVar) (TermMeta lang SymVar)

type SymTree lang a = Tree (DeltaEnv lang) a

-- | For ana to really be infinite, it should never return a term that
--  is only a metavariable; if that's ever the case, we should open that term
--  up in all of its constructors.
ana ::
  (LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Supply SymVar ->
  TermMeta lang SymVar ->
  SymTree lang (TermMeta lang SymVar)
ana defs s t@(hd `SystF.App` args) =
  case hd of
    SystF.Free (Builtin bin) ->
      undefined
    SystF.Free (TermSig n) ->
      case prtDefOf TermNamespace n `runReader` defs of
        DTypeDef _ -> error "Can't evaluate typedefs"
        DConstructor _ _ -> justEvaluateArgs
        DDestructor tyName -> anaDestructor defs s (unsafeUnDest t `runReader` defs)
        DFunction _ body _ ->
          undefined
    SystF.Meta vr -> do
      undefined -- here we'll need typing info and subsequently expanding all cases!

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

-- | Expanding a destructor is reasonably easy, but bureaucratic. The first
anaDestructor ::
  forall lang.
  (LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Supply SymVar ->
  UnDestMeta lang SymVar ->
  SymTree lang (TermMeta lang SymVar)
anaDestructor defs s (UnDestMeta _ _tyName _tyParams motive _ cases excess) =
  let (s0 : ss) = Supply.split s
   in Dest (ana defs s0 motive) $ \(ConstructorInfo _ consIx, consArgs) ->
        let caseTerm = appExcess (length consArgs) (cases !! consIx) excess
         in liftedTermAppN defs (ss !! consIx) caseTerm consArgs
  where
    -- If we're destructing a 'List Int' into a 'Unit -> Int', the term in question
    -- can be something like:
    -- > caseTerm = \x xs u -> x
    -- and @excess@ above will have a list of the excess arguments. A call to
    -- @appExcess 2 caseTerm excess@ will preserve the first 2 lambdas, then apply
    -- the excess arguments to the term, getting rid of them.
    -- This was mostly copied from Pirouette.Transformations.Term.removeExcessiveDestrArgs
    appExcess :: Int -> TermMeta lang SymVar -> [ArgMeta lang SymVar] -> TermMeta lang SymVar
    appExcess n (SystF.Lam ann ty t) = SystF.Lam ann ty . appExcess (n - 1) t . map (SystF.argMap id (shift 1))
    appExcess 0 t = SystF.appN t
    appExcess _ _ = error "Non-well formed destructor case"

mkMeta :: meta -> TermMeta lang meta
mkMeta m = SystF.Meta m `SystF.App` []

-- This is where most of the heavy lifting is done
liftedTermAppN ::
  forall lang.
  (LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  Supply SymVar ->
  TermMeta lang SymVar ->
  [SymTree lang (TermMeta lang SymVar)] ->
  SymTree lang (TermMeta lang SymVar)
liftedTermAppN defs s body args = do
  let body' = termMetaMap (pure . mkMeta) body
      args' = map (SystF.TermArg . mkMeta) args
      -- The resulting term is a term that has trees which
      -- contain further terms down its leaves
      res :: TermMeta lang (SymTree lang (TermMeta lang SymVar))
      res = SystF.appN body' args'
  aux <- termJoin <$> termMetaDistr res
  ana defs s aux

--    go :: (Show m) => [Tree (Term m)] -> Tree (Term m)
--    go targs = do
--      let body = cast $ gamma M.! r
--      res <- fmap termJoin $ termMetaDistr $ body `appN` (map meta targs)
--      ana gamma res

termMetaDistr :: (Applicative f) => TermMeta lang (f a) -> f (TermMeta lang a)
termMetaDistr = undefined

{-
This is how we open up the term in all of its possiblities, whenever we're met with
a single metavariable. It really shouldn't be the concern of the evaluation of
destructors:

        for3 ss consList cases $ \s' consNameTy caseTerm ->
          let (s'', delta, symbCons) = mkSymbolicCons s' (map typeFromMeta tyParams) consNameTy
              SystF.App _ symbArgs = symbCons
           in do
              t' <- stagedMotive
              Learn delta $
                Learn (Unify t' symbCons) $
                  ana defs s'' $ (caseTerm `SystF.appN` symbArgs) `SystF.appN` excess
-}

-- | Given a supply of names, a list of type arguments and a constructor name/type pair
-- we construct:
-- 1. a new supply of names, to be further used
-- 2. a delta to the environment, declaring the symbolic variables with their appropriate types
-- 3. a term consisting of the constructor applied to these symbolic arguments.
--
-- For example, @mkSymbolicCons s ["Int"] ("Cons", "all a . a -> List a -> List a")@
-- will return a new supply, a @DeclSymVar [("vx", "Int"), ("vxs", "List Int")]@
-- and a term @Cons $vx $vxs@.
mkSymbolicCons ::
  Supply SymVar ->
  [Type lang] ->
  (Name, Type lang) ->
  (Supply SymVar, DeltaEnv lang, TermMeta lang SymVar)
mkSymbolicCons sup tyParams (consName, consTy) =
  let instantiatedTy = SystF.tyInstantiateN consTy tyParams
      (consArgs, _) = SystF.tyFunArgs instantiatedTy
      (sup', svars) = freshSymVars sup consArgs
      symbArgs = map (SystF.TermArg . (`SystF.App` []) . SystF.Meta . fst) svars
      symbCons =
        SystF.App
          (SystF.Free $ TermSig consName)
          ( map (SystF.TyArg . typeToMeta) tyParams
              ++ symbArgs
          )
   in (sup', DeclSymVars svars, symbCons)

freshSymVars :: Supply SymVar -> [Type lang] -> (Supply SymVar, [(SymVar, Type lang)])
freshSymVars s [] = (s, [])
freshSymVars s tys =
  case take (length tys + 1) (Supply.split s) of
    [] -> error "impossible: take (n+1) of infinite list is non-nil"
    (s' : ss) ->
      let vars = zipWith (\i ty -> (Supply.supplyValue i, ty)) ss tys
       in (s', vars)

for3 :: [a] -> [b] -> [c] -> (a -> b -> c -> d) -> [d]
for3 as bs cs f = zipWith3 f as bs cs

secondM :: (Functor m) => (b -> m c) -> (a, b) -> m (a, c)
secondM f (x, y) = (x,) <$> f y
