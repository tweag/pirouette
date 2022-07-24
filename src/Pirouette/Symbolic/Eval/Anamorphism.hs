{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Anamorphism where

import Control.Applicative hiding (Const)
import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import Pirouette.Monad
import Pirouette.Symbolic.Eval.Types as X
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst (shift)
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Supply (Supply)
import qualified Supply

-- An example:
--
-- Let @$l@ denot that @l@ is a symbolic variable, let us explore how the
-- symbolic evaluation of the following expression would proceed:
--
-- > [| map (\x -> x + 1) $l |]
--
-- Initially, we see a function call and because we have to work for both
-- call-by-name and call-by-value languages, we represent that application
-- lifted to trees:
--
-- > Call (\a0 a1 -> [| defOf "map" a0 a1 |]) -- (A) here's the def of map, lifted to inline trees of terms
-- >      [ [| \x -> x + 1 |] -- (B) infinite evaluation of first argument
-- >      , [| $l |] -- (C) infinite evaluation of second argument
-- >      ]
--
-- Let's explore each different case in (A), (B) and (C) first and study their
-- nuances. Starting with (C) as it presents an interesting situation: because the semantics
-- of our terms, here, is grounded on infinite trees and the type of @$l@ is list of something,
-- we can't just return @Leaf $l@, intead we should expand one layer of @$l@ and return that:
--
-- > [| $l |] = Inst "$l" [ Cons "Nil" []
-- >                      , Learn (AddVars ["$l0", "$l1"]) (Cons "Cons" [ [| $l0 |], [| $l1 |] ])
-- >                      ]
--
-- Naturally, the evaluation of @[| $l1 |]@ will continue ad-infinitum, but because
-- we're in a lazy language, the thunks will remain unevaluated until we desire their result.
-- The evaluation of @[| $l0 |]@ is more interesting. Depending on its type if will remain
-- a symbolic variable forever: say its type is a builtin integer. There's no inductive structure
-- the anamorphism can use to expand it any further.
--
-- Looking at (B) next, we see a closure. Once again, we can't just return that closure. It denotes
-- a function that takes a term and returns that term plus one. Lited to trees, it will take a tree
-- and return that three with all its leaves added to one.
--
-- Type-wise, in Pirouette, the @Lam "x" (+ "x" 1)@ closure denotes a function of type:
--
-- > Term m -> Term m
--
-- It's denotation is: @\t -> subst "x" t (+ "x" 1)@ and given a term, it returns a term.
-- In the symbolic setting, we will have trees of terms instead, yielding a denotation in:
--
-- > Tree (Term m) -> Tree (Term m)
--
-- It gets a little bureaucratic but only relies on the monadic multiplication and
-- distributive law between @Tree@ and @Term@:
--
-- > [| \x -> x + 1 |] = Closure $ \(tx :: Tree (Term Sym)) ->
-- >    let body' = termMetaMap mkMeta "x + 1" :: Term (Tree (Term Sym))
-- >     in termJoin <$> termMetaDistr (SystF.app body' (SystF.TermArg . pure $ tx))
--
-- In reality we never really handle lambdas (TODO: why not? can't we start?) because
-- we get defunctionalized terms.

-- | A 'Tree' which denotes a set of pairs of @(monoid, leaf)@
data Tree lang monoid b
  = Empty
  | Leaf b
  | Learn monoid (Tree lang monoid b)
  | Union [Tree lang monoid b]
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
    forall a. Call ([Tree lang monoid a] -> Tree lang monoid b) [Tree lang monoid a]
  | -- | Destructors are also a little tricky, because in reality, we need to
    -- consume the motive until /at least/ the first constructor is found, that
    -- is the only guaranteed way to make any progress.
    forall a. Dest (Tree lang monoid a) ((ConstructorInfo, [Tree lang monoid a]) -> Tree lang monoid b)
  | -- | Naturally, to be able to effectively build a value with potentially infinite children,
    -- we also need torepresent constructors
    Cons ConstructorInfo [Tree lang monoid b]
  | -- | A Builtin is also something that we're stuck on until we decide to
    -- consume this tree
    Bin (BuiltinTerms lang) [Tree lang monoid b]
  | Const (Constants lang)

instance Show (Tree lang monoid a) where
  show _ = "Tree"

data ConstructorInfo = ConstructorInfo TyName Name Int

instance Functor (Tree lang m) where
  fmap _ Empty = Empty
  fmap _ (Const c) = Const c
  fmap f (Leaf x) = Leaf $ f x
  fmap f (Union ts) = Union $ map (fmap f) ts
  fmap f (Learn str t) = Learn str $ fmap f t
  fmap f (Call ts as) = Call (fmap f . ts) as
  fmap f (Dest motive worlds) = Dest motive (fmap f . worlds)
  fmap f (Cons c args) = Cons c (map (fmap f) args)
  fmap f (Bin c args) = Bin c (map (fmap f) args)

instance Applicative (Tree lang m) where
  pure = Leaf
  (<*>) = ap

instance Alternative (Tree lang m) where
  empty = Empty

  Empty <|> u = u
  t <|> Empty = t
  Union t <|> Union u = Union (t ++ u)
  Union t <|> u = Union (u : t)
  t <|> Union u = Union (t : u)
  t <|> u = Union [t, u]

instance Monad (Tree lang m) where
  Empty >>= _ = Empty
  Const c >>= _ = Const c
  Leaf x >>= f = f x
  Union ts >>= f = Union $ map (>>= f) ts
  Learn str t >>= f = Learn str (t >>= f)
  Call body args >>= f = Call (f <=< body) args
  Dest motive worlds >>= f = Dest motive (f <=< worlds)
  Cons c args >>= f = Cons c $ map (>>= f) args
  Bin c args >>= f = Bin c $ map (>>= f) args

treeDistr :: (Traversable t) => t (Tree lang m a) -> Tree lang m (t a)
treeDistr = sequenceA

data Env lang = Env
  { envSymVars :: [(SymVar, Type lang)],
    envConstraint :: [Constraint lang]
  }

data DeltaEnv lang
  = DeclSymVars (M.Map SymVar (Type lang))
  | Assign SymVar (TermMeta lang SymVar)

type SymTree lang a = Tree lang (DeltaEnv lang) a

symbolically ::
  forall lang.
  (LanguagePretty lang, LanguageSymEval lang) =>
  PrtUnorderedDefs lang ->
  TermMeta lang SymVar ->
  SymTree lang (TermMeta lang SymVar)
symbolically defs = runST $ do
  s0 <- Supply.newSupply (SymVar $ Name "s" (Just 0)) nextSymVar
  return (ana s0 M.empty)
  where
    nextSymVar (SymVar n) = SymVar (n {nameUnique = Just $ maybe 1 succ (nameUnique n)})

    -- For ana to really be infinite, it should never return a term that
    -- is only a metavariable; if that's ever the case, we should open that term
    -- up in all of its constructors.
    ana ::
      Supply SymVar ->
      M.Map SymVar (Type lang) ->
      TermMeta lang SymVar ->
      SymTree lang (TermMeta lang SymVar)
    ana s env t@(hd `SystF.App` args) =
      let sRec : sRest = Supply.split s
          args' = zipWith (`ana` env) sRest (mapMaybe SystF.fromArg args)
          rec = ana sRec env
       in case hd of
            SystF.Bound ann _ -> error $ "Can't evaluate bound variable: " ++ show ann
            SystF.Free Bottom -> Empty
            SystF.Free (Constant c) -> Const c
            SystF.Free (Builtin bin) -> Bin bin args'
            SystF.Free (TermSig n) ->
              case prtDefOf TermNamespace n `runReader` defs of
                DTypeDef _ -> error "Can't evaluate typedefs"
                DConstructor ix tyName -> Cons (ConstructorInfo tyName n ix) args'
                DDestructor _ -> anaDestructor s env (unsafeUnDest t `runReader` defs)
                DFunction _ body _ -> Call (liftedTermAppN (termToMeta body) >=> rec) args'
            SystF.Meta vr -> anaMeta sRec env vr
    ana _ _ t@SystF.Lam {} =
      error $
        unlines
          [ "Can't symbolically evaluate lambdas",
            "Did you not defunctionalize before?",
            "term: " ++ renderSingleLineStr (pretty t)
          ]
    ana _ _ t@SystF.Abs {} =
      error $
        unlines
          [ "Can't symbolically evaluate polymorphic terms",
            "Did you not monomorphize before?",
            "term: " ++ renderSingleLineStr (pretty t)
          ]

    -- Symbolically evaluating a match/case is trivial. Let @$m@ be the symbolic
    -- evaluation of the motive, we can lift the case semantics to being a function
    -- that given a constructor and its arguments, yields a new tree:
    --
    -- > forall a. Dest (Tree monoid a) ((ConstructorInfo, [Tree monoid a]) -> Tree monoid b)
    anaDestructor ::
      Supply SymVar ->
      M.Map SymVar (Type lang) ->
      UnDestMeta lang SymVar ->
      SymTree lang (TermMeta lang SymVar)
    anaDestructor s env (UnDestMeta _ _tyName _tyParams motive _ cases excess) =
      let (s0 : ss) = Supply.split s
       in Dest (ana s0 env motive) $ \(ConstructorInfo _ _ consIx, consArgs) ->
            let caseTerm = appExcess (length consArgs) (cases !! consIx) excess
             in liftedTermAppN caseTerm consArgs >>= ana (ss !! consIx) env
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

    anaMeta ::
      Supply SymVar ->
      M.Map SymVar (Type lang) ->
      SymVar ->
      SymTree lang (TermMeta lang SymVar)
    anaMeta s env target =
      case env M.! target of
        -- If the symvar is of type that we have a definition for, we can "eta-expand" it!
        -- Sat @target@ is of type @Either a b@, then:
        -- @symeval target == symeval (Left fresh) ++ symeval (Right fresh)@
        SystF.TyApp (SystF.Free (TySig tyName)) tyArgs ->
          let Datatype _ _ _ consList = prtTypeDefOf tyName `runReader` defs
           in Union $
                for2 (Supply.split s) consList $ \s' consNameTy ->
                  let (s'', delta, symbCons) = mkSymbolicCons s' (map typeFromMeta tyArgs) consNameTy
                      env' = M.unionWithKey (\k _ _ -> error $ "Conflicting names for: " ++ show k) env delta
                   in Learn (DeclSymVars delta) $
                        Learn (Assign target symbCons) $
                          ana s'' env' symbCons
        -- If this symvar is of any other type, we're done. This is as far as we can go.
        _ -> pure $ SystF.termPure $ SystF.Meta target

-- | Applies a term to tree arguments, yielding a tree of results.
liftedTermAppN ::
  forall lang.
  (LanguagePretty lang, LanguageSymEval lang) =>
  TermMeta lang SymVar ->
  [SymTree lang (TermMeta lang SymVar)] ->
  SymTree lang (TermMeta lang SymVar)
liftedTermAppN body args = do
  let body' = termMetaMap (pure . mkMeta) body
      args' = map (SystF.TermArg . mkMeta) args
      -- The resulting term is a term that has trees which
      -- contain further terms down its leaves
      res :: TermMeta lang (SymTree lang (TermMeta lang SymVar))
      res = SystF.appN body' args'
  termJoin <$> termMetaDistr res
  where
    mkMeta :: meta -> TermMeta lang meta
    mkMeta m = SystF.Meta m `SystF.App` []

termMetaDistr :: (Applicative f) => TermMeta lang (f a) -> f (TermMeta lang a)
termMetaDistr (SystF.Lam ann ty t) = SystF.Lam ann (typeUnsafeCastMeta ty) <$> termMetaDistr t
termMetaDistr (SystF.Abs ann ki t) = SystF.Abs ann ki <$> termMetaDistr t
termMetaDistr (SystF.App hd args) = SystF.App <$> doVar hd <*> traverse doArgs args
  where
    doArgs :: (Applicative f) => SystF.Arg (TypeMeta lang (f a)) (TermMeta lang (f a)) -> f (ArgMeta lang a)
    doArgs (SystF.TyArg ty) = pure $ SystF.TyArg $ typeUnsafeCastMeta ty
    doArgs (SystF.TermArg t) = SystF.TermArg <$> termMetaDistr t

    doVar :: (Applicative f) => SystF.VarMeta (f a) name base -> f (SystF.VarMeta a name base)
    doVar (SystF.Meta fa) = SystF.Meta <$> fa
    doVar (SystF.Free b) = pure $ SystF.Free b
    doVar (SystF.Bound ann i) = pure $ SystF.Bound ann i

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
  (Supply SymVar, M.Map SymVar (Type lang), TermMeta lang SymVar)
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
   in (sup', M.fromList svars, symbCons)

freshSymVars :: Supply SymVar -> [Type lang] -> (Supply SymVar, [(SymVar, Type lang)])
freshSymVars s [] = (s, [])
freshSymVars s tys =
  case take (length tys + 1) (Supply.split s) of
    [] -> error "impossible: take (n+1) of infinite list is non-nil"
    (s' : ss) ->
      let vars = zipWith (\i ty -> (Supply.supplyValue i, ty)) ss tys
       in (s', vars)

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 as bs f = zipWith f as bs

for3 :: [a] -> [b] -> [c] -> (a -> b -> c -> d) -> [d]
for3 as bs cs f = zipWith3 f as bs cs

secondM :: (Functor m) => (b -> m c) -> (a, b) -> m (a, c)
secondM f (x, y) = (x,) <$> f y
