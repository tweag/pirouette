{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Anamorphism where

import Control.Monad.Reader
import Control.Monad.ST
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import Debug.Trace
import Pirouette.Monad hiding (WHNFConstant)
import Pirouette.Symbolic.Eval.Types
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

data AnaEnv lang = AnaEnv
  { gamma :: M.Map SymVar (Type lang),
    knowns :: M.Map SymVar (TermMeta lang SymVar)
  }

symbolically ::
  forall lang.
  (Language lang) =>
  PrtUnorderedDefs lang ->
  Term lang ->
  TermSet lang
symbolically defs = runST $ do
  s0 <- Supply.newSupply 0 succ
  return (withSymVars s0)
  where
    withSymVars ::
      Supply Int ->
      Term lang ->
      TermSet lang
    withSymVars s t =
      let (args, _) = SystF.getHeadLams t
          (s', svars) = freshSymVars s (map (typeToMeta . snd) args)
          body =
            SystF.appN (termToMeta t) $
              map (SystF.TermArg . SystF.termPure . SystF.Meta . fst) svars
       in TermSet $
            declSymVars (M.fromList svars) $
              unTermSet $
                termTree (AnaEnv (M.fromList svars) M.empty) s' body

    termTree ::
      AnaEnv lang ->
      Supply Int ->
      TermMeta lang SymVar ->
      TermSet lang
    termTree env s t = trace inf $ TermSet $ termTreeAux s env t
      where
        inf = unlines ["termTree:", renderSingleLineStr (pretty t)]

    termTreeAux ::
      Supply Int ->
      AnaEnv lang ->
      TermMeta lang SymVar ->
      Tree (DeltaEnv lang) (Spine lang (TermSet lang))
    termTreeAux _ _ SystF.Lam {} = error "Lam has no tree"
    termTreeAux _ _ SystF.Abs {} = error "Abs has no tree"
    -- TODO: What do we do with args here? I think it must always be empty: symbolic variables
    -- will never be of function type, at least for sure not until we add closures... or will they?
    termTreeAux s env (SystF.Meta tgt `SystF.App` _args)
      | Just res <- M.lookup tgt (knowns env) = pure $ termSpine s (termTree env) res
      | otherwise =
        case gamma env M.! tgt of
          -- If the symvar is of type that we have a definition for, we can "eta-expand" it!
          -- Sat @target@ is of type @Either a b@, then:
          -- @symeval target == symeval (Left fresh) ++ symeval (Right fresh)@
          SystF.TyApp (SystF.Free (TySig tyName)) tyArgs ->
            let Datatype _ _ _ consList = prtTypeDefOf tyName `runReader` defs
             in Union $
                  for2 (Supply.split s) consList $ \s' consNameTy ->
                    let (s'', delta, symbCons) = mkSymbolicCons s' (map typeFromMeta tyArgs) consNameTy
                        gamma' = M.unionWithKey (\k _ _ -> error $ "Conflicting names for: " ++ show k) (gamma env) delta
                        env' = AnaEnv gamma' (M.insert tgt symbCons (knowns env))
                     in declSymVars delta $
                          Learn (Assign tgt symbCons) $
                            pure $
                              termSpine s'' (termTree env') symbCons
          -- If this symvar is of any other type, we're done. This is as far as we can go.
          -- Maybe we need a dedicated constructor for this. We should mark that this is really stuck
          -- and there's nothing else to do.
          _ -> pure $ Head (WHNFSymVar tgt) []
    termTreeAux s env t = pure $ termSpine s (termTree env) t

    -- A spine can be thought of as the parts without any choice: there's only one thing to do: evaluate.
    termSpine ::
      forall meta.
      (Show meta, Pretty meta) =>
      Supply Int ->
      (Supply Int -> TermMeta lang meta -> TermSet lang) ->
      TermMeta lang meta ->
      Spine lang (TermSet lang)
    termSpine _ _ SystF.Lam {} = error "Lam has no spine"
    termSpine _ _ SystF.Abs {} = error "Abs has no spine"
    termSpine s f t0@(hd `SystF.App` args) =
      let sHd : sHd' : sTl = Supply.split s
          args' = mapMaybe (\(s', t) -> fmap (f s') . SystF.fromArg $ t) (zip sTl args)
       in case hd of
            SystF.Bound ann _ -> error $ "Bound has no spine" ++ show ann
            SystF.Free (TermSig n) ->
              case prtDefOf TermNamespace n `runReader` defs of
                DTypeDef _ -> error "TypeDef has no spine"
                -- The spine of a destructor is its semantics upon finding a constructor in the motive
                DDestructor _ ->
                  let UnDestMeta _ _tyName _tyParams motive _ cases excess = unsafeUnDest t0 `runReader` defs
                   in flip Dest (f sHd motive) $ \(ConstructorInfo _ _ consIx, consArgs) ->
                        let caseTerm = appExcess (length consArgs) (cases !! consIx) excess
                         in Next $ liftedTermAppN sHd' f caseTerm consArgs
                -- Similarly to functions, but here we'll ignore all type arguments
                DFunction _ body _ ->
                  Call n (Next . liftedTermAppN sHd f (termToMeta body)) args'
                -- Constructors are trivial:
                DConstructor ix tyName ->
                  Head (WHNFCotr $ ConstructorInfo tyName n ix) $ map Next args'
            SystF.Free (Builtin bin) -> Head (WHNFBuiltin bin) $ map Next args'
            SystF.Free Bottom -> Head WHNFBottom $ map Next args'
            SystF.Free (Constant x) -> Head (WHNFConst x) []
            -- TODO: we're ignoring the arguments of our metavariable... is this ok?
            -- I think so, since metavariables can never be of function type anyway.
            -- Therefore, they'll never be applied.
            SystF.Meta _ -> Next $ f s t0

    -- If we're destructing a 'List Int' into a 'Unit -> Int', the term in question
    -- can be something like:
    -- > caseTerm = \x xs u -> x
    -- and @excess@ above will have a list of the excess arguments. A call to
    -- @appExcess 2 caseTerm excess@ will preserve the first 2 lambdas, then apply
    -- the excess arguments to the term, getting rid of them.
    -- This was mostly copied from Pirouette.Transformations.Term.removeExcessiveDestrArgs
    appExcess :: forall meta. (Show meta) => Int -> TermMeta lang meta -> [ArgMeta lang meta] -> TermMeta lang meta
    appExcess n (SystF.Lam ann ty t) = SystF.Lam ann ty . appExcess (n - 1) t . map (SystF.argMap id (shift 1))
    appExcess 0 t = SystF.appN t
    appExcess _ _ = error "Non-well formed destructor case"

declSymVars :: M.Map SymVar (Type lang) -> Tree (DeltaEnv lang) a -> Tree (DeltaEnv lang) a
declSymVars vs
  | not (M.null vs) = Learn (DeclSymVars vs)
  | otherwise = id

termSetAbsorb :: TermMeta lang (TermSet lang) -> TermSet lang
termSetAbsorb =
  TermSet
    . fmap (fmap termSetAbsorb . termMetaDistr)
    . termMetaDistr
    . termMetaMap unTermSet
  where
    termMetaDistr :: (Applicative f) => TermMeta lang (f a) -> f (TermMeta lang a)
    termMetaDistr (SystF.Lam ann ty t) = SystF.Lam ann (typeUnsafeCastMeta ty) <$> termMetaDistr t
    termMetaDistr (SystF.Abs ann ki t) = SystF.Abs ann ki <$> termMetaDistr t
    termMetaDistr (SystF.App hd args0) = SystF.App <$> doVar hd <*> traverse doArgs args0
      where
        doArgs ::
          (Applicative f) =>
          SystF.Arg (TypeMeta lang (f a)) (TermMeta lang (f a)) ->
          f (ArgMeta lang a)
        doArgs (SystF.TyArg ty) = pure $ SystF.TyArg $ typeUnsafeCastMeta ty
        doArgs (SystF.TermArg t) = SystF.TermArg <$> termMetaDistr t

        doVar :: (Applicative f) => SystF.VarMeta (f a) name base -> f (SystF.VarMeta a name base)
        doVar (SystF.Meta fa) = SystF.Meta <$> fa
        doVar (SystF.Free b) = pure $ SystF.Free b
        doVar (SystF.Bound ann i) = pure $ SystF.Bound ann i

{-
magic ::
  TermMeta lang meta ->
  [args] ->
  res
magic body args =
  let body' = termMetaMap Left body
   in _
-}

-- | Lifts term application to termsets.
liftedTermAppN ::
  forall lang meta.
  (Language lang, Pretty meta) =>
  Supply Int ->
  (Supply Int -> TermMeta lang meta -> TermSet lang) ->
  TermMeta lang meta ->
  [TermSet lang] ->
  TermSet lang
liftedTermAppN s go body args =
  let (s0, s1) = Supply.split2 s
      body' = termMetaMap (go s0 . mkMeta) body
      args' = map (SystF.TermArg . mkMeta) args

      foo :: TermMeta lang (TermSet lang)
      foo = body' `SystF.appN` args'

      res = termSetAbsorb foo
   in trace (information res) res
  where
    mkMeta = (`SystF.App` []) . SystF.Meta

    information x =
      unlines $
        [ "liftedTermAppN:",
          "  term: " ++ renderSingleLineStr (pretty body),
          "  args: "
        ]
          ++ map (("  - " ++) . show) args
          ++ ["  res: " ++ show x]

{-
termSetAbsorb (SystF.Lam ann ty t) = SystF.Lam ann (typeUnsafeCastMeta ty) <$> termMetaDistr t
termSetAbsorb (SystF.Abs ann ki t) = SystF.Abs ann ki <$> termMetaDistr t
termSetAbsorb (SystF.App hd args0) = SystF.App <$> doVar hd <*> traverse doArgs args0
  where
    doArgs ::
      (Applicative f) =>
      SystF.Arg (TypeMeta lang (f a)) (TermMeta lang (f a)) ->
      f (ArgMeta lang a)
    doArgs (SystF.TyArg ty) = pure $ SystF.TyArg $ typeUnsafeCastMeta ty
    doArgs (SystF.TermArg t) = SystF.TermArg <$> termMetaDistr t

    doVar :: (Applicative f) => SystF.VarMeta (f a) name base -> f (SystF.VarMeta a name base)
    doVar (SystF.Meta fa) = SystF.Meta <$> fa
    doVar (SystF.Free b) = pure $ SystF.Free b
    doVar (SystF.Bound ann i) = pure $ SystF.Bound ann i
-}

{-
-- | Applies a term to tree arguments, yielding a tree of results.
liftedTermAppN ::
  forall lang meta f.
  (Language lang, Applicative f, Show (f (TermMeta lang meta)), Show meta, Pretty meta) =>
  TermMeta lang meta ->
  [f (TermMeta lang meta)] ->
  f (TermMeta lang meta)
liftedTermAppN body args =
  let body' = termMetaMap (pure . mkMeta) body
      args' = map (SystF.TermArg . mkMeta) args
      res = termJoin <$> termMetaDistr (SystF.appN body' args')
   in trace (information res) res
  where
    information x =
      unlines $
        [ "liftedTermAppN:",
          "  term: " ++ renderSingleLineStr (pretty body),
          "  args: "
        ]
          ++ map (("  - " ++) . show) args
          ++ ["  res: " ++ show x]

    mkMeta :: m -> TermMeta lang m
    mkMeta m = SystF.Meta m `SystF.App` []

    -- This function is local because it makes manya assumptios about where metavariables
    -- occur. In this case, we assume they won't ever appear on types, so its safe to just
    -- unsafeCoerce the types and avoid traversing them. In that sense, it's not /really/
    -- a universal distributive law, only when the types have no metas.
    termMetaDistr :: (Applicative f) => TermMeta lang (f a) -> f (TermMeta lang a)
    termMetaDistr (SystF.Lam ann ty t) = SystF.Lam ann (typeUnsafeCastMeta ty) <$> termMetaDistr t
    termMetaDistr (SystF.Abs ann ki t) = SystF.Abs ann ki <$> termMetaDistr t
    termMetaDistr (SystF.App hd args0) = SystF.App <$> doVar hd <*> traverse doArgs args0
      where
        doArgs ::
          (Applicative f) =>
          SystF.Arg (TypeMeta lang (f a)) (TermMeta lang (f a)) ->
          f (ArgMeta lang a)
        doArgs (SystF.TyArg ty) = pure $ SystF.TyArg $ typeUnsafeCastMeta ty
        doArgs (SystF.TermArg t) = SystF.TermArg <$> termMetaDistr t

        doVar :: (Applicative f) => SystF.VarMeta (f a) name base -> f (SystF.VarMeta a name base)
        doVar (SystF.Meta fa) = SystF.Meta <$> fa
        doVar (SystF.Free b) = pure $ SystF.Free b
        doVar (SystF.Bound ann i) = pure $ SystF.Bound ann i
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
  Supply Int ->
  [Type lang] ->
  (Name, Type lang) ->
  (Supply Int, M.Map SymVar (Type lang), TermMeta lang SymVar)
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

-- | Given a list of types, split the supply into enough parts to be able to
-- issue a name for each type and a new supply that should be used for any further
-- supply-oriented operations.
freshSymVars :: Supply Int -> [Type lang] -> (Supply Int, [(SymVar, Type lang)])
freshSymVars s [] = (s, [])
freshSymVars s tys =
  case take (length tys + 1) (Supply.split s) of
    [] -> error "impossible: take (n+1) of infinite list is non-nil"
    (s' : ss) ->
      let vars = zipWith (\i ty -> (supplySymVar i, ty)) ss tys
       in (s', vars)
  where
    supplySymVar :: Supply Int -> SymVar
    supplySymVar = SymVar . Name "s" . Just . Supply.supplyValue

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 as bs f = zipWith f as bs

for3 :: [a] -> [b] -> [c] -> (a -> b -> c -> d) -> [d]
for3 as bs cs f = zipWith3 f as bs cs

secondM :: (Functor m) => (b -> m c) -> (a, b) -> m (a, c)
secondM f (x, y) = (x,) <$> f y
