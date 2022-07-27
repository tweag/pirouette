{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Symbolic.Eval.Anamorphism where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import Debug.Trace
import Pirouette.Monad
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

symbolically ::
  forall lang.
  (Language lang) =>
  PrtUnorderedDefs lang ->
  Term lang ->
  TermSet lang SymVar
symbolically defs = runST $ do
  s0 <- Supply.newSupply (SymVar $ Name "s" (Just 0)) nextSymVar
  return (withSymVars s0)
  where
    nextSymVar (SymVar n) = SymVar (n {nameUnique = Just $ maybe 1 succ (nameUnique n)})

    withSymVars ::
      Supply SymVar ->
      Term lang ->
      TermSet lang SymVar
    withSymVars s t =
      let (args, _) = SystF.getHeadLams t
          (s', svars) = freshSymVars s (map (typeToMeta . snd) args)
          body =
            SystF.appN (termToMeta t) $
              map (SystF.TermArg . SystF.termPure . SystF.Meta . fst) svars
       in declSymVars (M.fromList svars) $ ana s' (M.fromList svars) M.empty body

    ana ::
      Supply SymVar ->
      M.Map SymVar (Type lang) ->
      M.Map SymVar (TermMeta lang SymVar) ->
      TermMeta lang SymVar ->
      TermSet lang SymVar
    ana s env knowns t = undefined
      where
        -- trace str $ ana' s env knowns t

        str =
          unlines
            [ "term: " ++ renderSingleLineStr (pretty t),
              "  env: " ++ renderSingleLineStr (pretty $ M.toList env),
              "  knowns: " ++ renderSingleLineStr (pretty $ M.toList knowns)
            ]

    -- For ana to really be infinite, it should never return a term that
    -- is only a metavariable; if that's ever the case, we should open that term
    -- up in all of its constructors.
    ana' ::
      Supply SymVar ->
      M.Map SymVar (Type lang) ->
      M.Map SymVar (TermMeta lang SymVar) ->
      TermMeta lang SymVar ->
      TermTree lang SymVar (TermMeta lang SymVar)
    ana' s env knowns t@(hd `SystF.App` args) =
      let sRec : sRest = Supply.split s
          -- TODO: how do we communicate in between the arguments? Take the following call as an example:
          -- > add $s0 (Suc $s0)
          -- We'll evaluate each argument separately, which is not ideal.
          termArgs = mapMaybe SystF.fromArg args
          args' = zipWith (\s0 -> ana' s0 env knowns) sRest termArgs
       in -- TODO: can't constructors loop on this?!
          -- doCall callHd term = Call callHd (liftedTermAppN term >=> ana sRec env knowns) args'
          case hd of
            SystF.Bound ann _ -> error $ "Can't evaluate bound variable: " ++ show ann
            SystF.Free (TermSig n) ->
              case prtDefOf TermNamespace n `runReader` defs of
                DDestructor _ -> anaDestructor s env knowns (unsafeUnDest t `runReader` defs)
                DTypeDef _ -> error "Can't evaluate typedefs"
                DConstructor ix tyName ->
                  TermTree $ pure $ WHNF (WHNFCotr $ ConstructorInfo tyName n ix) termArgs
                DFunction _ body _ ->
                  TermTree $ pure $ Call n (liftedTermAppN (termToMeta body) >=> ana' sRec env knowns) args'
            SystF.Free (Builtin bin) -> undefined -- doCall (CallBuiltin bin) (SystF.termPure hd)
            SystF.Free Bottom -> pure t
            SystF.Free (Constant _) -> pure t
            SystF.Meta vr -> undefined -- anaMeta sRec env knowns vr
    ana' _ _ _ t@SystF.Lam {} =
      error $
        unlines
          [ "Can't symbolically evaluate lambdas",
            "Did you not defunctionalize before?",
            "term: " ++ renderSingleLineStr (pretty t)
          ]
    ana' _ _ _ t@SystF.Abs {} =
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
      M.Map SymVar (TermMeta lang SymVar) ->
      UnDestMeta lang SymVar ->
      TermTree lang SymVar (TermMeta lang SymVar)
    anaDestructor s env knowns (UnDestMeta _ _tyName _tyParams motive _ cases excess) =
      let (s0 : ss) = Supply.split s
       in undefined
      where
        --   flip Dest (ana s0 env knowns motive) $ \(ConstructorInfo _ _ consIx, consArgs) ->
        --     let caseTerm = appExcess (length consArgs) (cases !! consIx) excess
        --      in liftedTermAppN caseTerm consArgs -- >>= ana (ss !! consIx) env knowns

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
      M.Map SymVar (TermMeta lang SymVar) ->
      SymVar ->
      TermTree lang SymVar (TermMeta lang SymVar)
    anaMeta s env knowns target
      | Just res <- M.lookup target knowns = undefined -- pure res
      | otherwise =
        case env M.! target of
          -- If the symvar is of type that we have a definition for, we can "eta-expand" it!
          -- Sat @target@ is of type @Either a b@, then:
          -- @symeval target == symeval (Left fresh) ++ symeval (Right fresh)@
          SystF.TyApp (SystF.Free (TySig tyName)) tyArgs ->
            let Datatype _ _ _ consList = prtTypeDefOf tyName `runReader` defs
             in undefined
          --   Union $
          --     for2 (Supply.split s) consList $ \s' consNameTy ->
          --       let (s'', delta, symbCons) = mkSymbolicCons s' (map typeFromMeta tyArgs) consNameTy
          --           env' = M.unionWithKey (\k _ _ -> error $ "Conflicting names for: " ++ show k) env delta
          --        in declSymVars delta $
          --             Learn (Assign target symbCons) $
          --               ana s'' env' (M.insert target symbCons knowns) symbCons
          -- If this symvar is of any other type, we're done. This is as far as we can go.
          -- Maybe we need a dedicated constructor for this. We should mark that this is really stuck
          -- and there's nothing else to do.
          _ -> pure $ SystF.termPure $ SystF.Meta target

declSymVars :: M.Map SymVar (Type lang) -> TermSet lang meta -> TermSet lang meta
declSymVars vs
  | not (M.null vs) = undefined -- Learn (DeclSymVars vs)
  | otherwise = id

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

    termMetaUnDistr :: (Applicative f) => f (TermMeta lang a) -> TermMeta lang (f a)
    termMetaUnDistr = undefined

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

-- | Given a list of types, split the supply into enough parts to be able to
-- issue a name for each type and a new supply that should be used for any further
-- supply-oriented operations.
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
