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
            SystF.appN (termToMeta t) $ map (SystF.TermArg . termMeta . fst) svars
       in Learn (DeclSymVars $ M.fromList svars) $
            evalChooseLoop s' (AnaEnv (M.fromList svars) M.empty) body

    evalChooseLoop :: Supply Int -> AnaEnv lang -> TermMeta lang SymVar -> TermSet lang
    evalChooseLoop = eval choose

    eval ::
      forall meta.
      (Show meta) =>
      (Supply Int -> AnaEnv lang -> meta -> TermSet lang) ->
      Supply Int ->
      AnaEnv lang ->
      TermMeta lang meta ->
      TermSet lang
    eval _ _ _ SystF.Lam {} = error "Lam has no eval"
    eval _ _ _ SystF.Abs {} = error "Abs has no eval"
    eval f s env t0@(SystF.App hd args) =
      let s0 : ss = Supply.split s

          evalL :: [SystF.Arg ty (TermMeta lang meta)] -> [TermSet lang]
          evalL = zipWith (\s' -> eval f s' env) ss . mapMaybe SystF.fromArg
       in case hd of
            SystF.Bound ann _ -> error $ "Bound has no spine" ++ show ann
            SystF.Meta meta -> f s env meta
            SystF.Free (Builtin _bin) -> undefined
            SystF.Free (Constant _x) -> undefined
            SystF.Free Bottom -> Spine WHNFBottom
            SystF.Free (TermSig n) ->
              case prtDefOf TermNamespace n `runReader` defs of
                DTypeDef _ -> error "TypeDef has no spine"
                DConstructor ix tyName ->
                  Spine $ WHNFCotr (ConstructorInfo tyName n ix) $ evalL args
                DDestructor _ ->
                  let UnDestMeta _ _tyName _tyParams motive _ cases excess = unsafeUnDest t0 `runReader` defs
                      s1 : s2 : _ = ss
                   in flip Dest (eval f s0 env motive) $ \(ConstructorInfo _ _ consIx, consArgs) ->
                        let caseTerm = appExcess (length consArgs) (cases !! consIx) excess
                         in liftedTermAppN' s1 env (termMetaMapUnique (`f` env) s2 caseTerm) consArgs
                DFunction _ body _ ->
                  Call (liftedTermAppN s0 env (termToMeta body)) $ evalL args

    choose :: Supply Int -> AnaEnv lang -> SymVar -> TermSet lang
    choose s env meta = Inst meta $ do
      -- If the symvar is of type that we have a definition for, we can "eta-expand" it!
      -- Sat @target@ is of type @Either a b@, then:
      -- @symeval target == symeval (Left fresh) ++ symeval (Right fresh)@
      SystF.TyApp (SystF.Free (TySig tyName)) tyArgs <- M.lookup meta (gamma env)
      let Datatype _ _ _ consList = prtTypeDefOf tyName `runReader` defs
      return $
        Union $
          for2 (Supply.split s) consList $ \s' consNameTy ->
            let (s'', delta, symbCons) = mkSymbolicCons s' (map typeFromMeta tyArgs) consNameTy
                gamma' = M.unionWithKey (\k _ _ -> error $ "Conflicting names for: " ++ show k) (gamma env) delta
                env' = AnaEnv gamma' (M.insert meta symbCons (knowns env))
             in declSymVars delta $
                  Learn (Assign meta symbCons) $
                    evalChooseLoop s'' env' symbCons

    liftedTermAppN' ::
      Supply Int ->
      AnaEnv lang ->
      TermMeta lang (TermSet lang) ->
      [TermSet lang] ->
      TermSet lang
    liftedTermAppN' s env body args =
      eval (\_ _ -> id) s env (termMetaMap (either id id) $ genericTermApp body args)

    liftedTermAppN ::
      Supply Int ->
      AnaEnv lang ->
      TermMeta lang SymVar ->
      [TermSet lang] ->
      TermSet lang
    liftedTermAppN s env body args =
      let (s1, s2) = Supply.split2 s
       in eval (\_ _ -> id) s2 env (termMetaMapUnique (\s' -> either (choose s' env) id) s1 $ genericTermApp body args)

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

declSymVars :: M.Map SymVar (Type lang) -> TermSet lang -> TermSet lang
declSymVars vs
  | not (M.null vs) = Learn (DeclSymVars vs)
  | otherwise = id

genericTermApp ::
  (LanguageBuiltins lang, Show meta, Show arg) =>
  TermMeta lang meta ->
  [arg] ->
  TermMeta lang (Either meta arg)
genericTermApp body args =
  let body' = termMetaMap Left body
      args' = map (SystF.TermArg . termMeta . Right) args
   in body' `SystF.appN` args'

termMetaMapUnique ::
  (Supply s -> m -> m') ->
  Supply s ->
  TermMeta lang m ->
  TermMeta lang m'
termMetaMapUnique f s0 (SystF.Abs ann ki t) =
  SystF.Abs ann ki (termMetaMapUnique f s0 t)
termMetaMapUnique f s0 (SystF.Lam ann ty t) =
  let (s1, s2) = Supply.split2 s0
   in SystF.Lam ann (typeMetaMapUnique f s1 ty) (termMetaMapUnique f s2 t)
termMetaMapUnique f s0 (SystF.App hd args) =
  let s : ss = Supply.split s0
   in SystF.App (SystF.varMapMeta (f s) hd) $
        zipWith (\s' -> SystF.argMap (typeMetaMapUnique f s') (termMetaMapUnique f s')) ss args

typeMetaMapUnique ::
  (Supply s -> m -> m') ->
  Supply s ->
  TypeMeta lang m ->
  TypeMeta lang m'
typeMetaMapUnique f s (SystF.TyLam ann ki t) =
  SystF.TyLam ann ki $ typeMetaMapUnique f s t
typeMetaMapUnique f s (SystF.TyAll ann ki t) =
  SystF.TyAll ann ki $ typeMetaMapUnique f s t
typeMetaMapUnique f s0 (SystF.TyFun a b) =
  let (s1, s2) = Supply.split2 s0
   in SystF.TyFun (typeMetaMapUnique f s1 a) (typeMetaMapUnique f s2 b)
typeMetaMapUnique f s0 (SystF.TyApp hd args) =
  let s : ss = Supply.split s0
   in SystF.TyApp (SystF.varMapMeta (f s) hd) $ zipWith (typeMetaMapUnique f) ss args

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
