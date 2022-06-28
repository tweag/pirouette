{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.Transformations where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad.Except
import Data.Data
import Data.Functor
import Data.Generics.Uniplate.Data
import Data.List (elemIndex)
import Data.String (fromString)
import Pirouette.Monad
import Pirouette.Monad.Maybe
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import qualified Pirouette.Term.Syntax.SystemF as SystF

-- | Put excessive arguments of a a destructor in the branches.
--  Because we have n-ary applications, whenever we translate something like:
--
--  > t = ([[[d/Nat n] (\b -> if b then 0 else 1) (\n b -> if b then n else 0)] True])
--
--  We get:
--
--  > u = [d/Nat n (\b -> if b then 0 else 1) (\n b -> if b then n else 0) True]
--
--  Now, that makes it difficult to swap destructors around since we can only do so
--  when it is in WHNF destructor applications (which forbids over-application).
--  Moreover, it makes the code larger and more difficult to read.
--
--  Hence, calling 'removeExcessiveDestArgs u' will return:
--
--  > v = [d/Nat n (if b then 0 else 1)[b := True] (\n -> if b then n else 0)[b := True]]
--  > v = [d/Nat n 0 (\n -> n)]
--
--  Since the second constructor of Nat is Succ :: Nat -> Nat, one does not want to
--  simply apply (\n b -> if b then n else 0) to True, since the first abstraction
--  corresponds to the argument of Succ.
--
--  Whenever a constructor has no arguments, its destruction in PlutusIR is done using
--  a function which takes an argument of type `Unit`, like:
--
--  > t = ([[[d/Bool x] (\thunk -> T) (\thunk -> F)] Unit])
--
--  We get:
--
--  > u = [d/Bool x (\thunk -> T) (\thunk -> F) Unit]
--  Because PlutusIR is meant to be executed in a strict fashion, these thunks are there
--  to prevent evaluation. For us, it really doesn't matter since we will symbolically evaluate it.
--
--  Hence, calling 'removeExcessiveDestArgs u' will return:
--
--  > v = [d/Bool x T[thunk := Unit] F[thunk := Unit]]
--  Generally v = [d/Bool T F] since `thunk` has no reason to appear in `T` and `F`.
removeExcessiveDestArgs :: (Show meta, Data meta, Typeable meta, PirouetteReadDefs lang m) => TermMeta lang meta -> m (TermMeta lang meta)
removeExcessiveDestArgs = rewriteM (runMaybeT . go)
  where
    go :: (Show meta, PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (TermMeta lang meta)
    go t = do
      UnDestMeta n tyN tyArgs x tyReturn cases excess <- unDest t
      if null excess
        then fail "No excessive destr arguments"
        else do
          Datatype _ _ _ cons <- lift (prtTypeDefOf tyN)
          let cons' = map (second typeToMeta) cons
          return $
            SystF.App (SystF.Free $ TermSig n) $
              map SystF.TyArg tyArgs
                ++ [SystF.TermArg x, SystF.TyArg $ tyDrop (length excess) tyReturn]
                ++ zipWith (\(_, cty) t0 -> SystF.TermArg $ appExcessive excess cty t0) cons' cases

    -- Receives the excessive arguments, the type of the constructor whose case we're on and
    -- the term defining the value at this constructor's case.
    appExcessive :: (Show meta, LanguageBuiltins lang) => [ArgMeta lang meta] -> TypeMeta lang meta -> TermMeta lang meta -> TermMeta lang meta
    appExcessive l (SystF.TyFun _ b) (SystF.Lam n ty t) =
      SystF.Lam n ty (appExcessive (map (SystF.argMap id (shift 1)) l) b t) -- `a` and `ty` are equal, up to substitution of variables in the type of the constructors.
    appExcessive _ (SystF.TyFun _ _) _ =
      error "Ill-typed program! Number of lambdas in case-branch must be bigger than constructor arity"
    appExcessive l _ t =
      SystF.appN t l

    tyDrop :: Int -> TypeMeta lang meta -> TypeMeta lang meta
    tyDrop 0 t = t
    tyDrop n (SystF.TyFun _ b) = tyDrop (n - 1) b
    tyDrop n (SystF.TyAll _ _ t) = tyDrop (n - 1) t
    tyDrop _ _ = error "Ill-typed program: not enough type parameters to drop"

-- | Because TLA+ really doesn't allow for shadowed bound names, we need to rename them
--  after performing any sort of inlining.
deshadowBoundNames :: Term lang -> Term lang
deshadowBoundNames = deshadowBoundNamesWithForbiddenNames []

deshadowBoundNamesWithForbiddenNames :: [Name] -> Term lang -> Term lang
deshadowBoundNamesWithForbiddenNames = go []
  where
    -- @newAnnFrom ns n@ returns a fresh name similar to @n@ given a list of declared names @ns@.
    -- it does so by incrementing the 'nameUnique' part of 'n'. Instead of incrementing one-by-one,
    -- we increment by i to hopefully require less iterations to find a fresh name.
    newAnnFrom :: [Name] -> [Name] -> Name -> Name
    newAnnFrom anns forbidden a =
      case a `elemIndex` (anns ++ forbidden) of
        Nothing -> a
        Just i -> newAnnFrom anns forbidden (a {nameUnique = Just $ maybe i ((+ i) . (+ 1)) (nameUnique a)})

    go bvs forbidden (SystF.Lam (SystF.Ann ann) ty t) =
      let ann' = newAnnFrom bvs forbidden ann
       in SystF.Lam (SystF.Ann ann') ty (go (ann' : bvs) forbidden t)
    go bvs forbidden (SystF.Abs a ki t) = SystF.Abs a ki (go bvs forbidden t)
    go bvs forbidden (SystF.App n args) =
      let args' = map (SystF.argMap id (go bvs forbidden)) args
          n' =
            case n of
              SystF.Bound _x i ->
                if fromInteger i >= length bvs
                  then n
                  else SystF.Bound (SystF.Ann (unsafeIdx "deshadowBoundNames" bvs i)) i
              _ -> n
       in SystF.App n' args'

-- | Expand all non-recursive definitions
expandDefs ::
  forall lang m.
  (PirouetteReadDefs lang m, Pretty (Constants lang), Pretty (BuiltinTerms lang), Pretty (BuiltinTypes lang)) =>
  Term lang ->
  m (Term lang)
expandDefs = fmap deshadowBoundNames . rewriteM (runMaybeT . go)
  where
    go :: Term lang -> MaybeT m (Term lang)
    go (SystF.App (SystF.Free (TermSig n)) args) = do
      isRec <- lift $ termIsRecursive n
      if isRec
        then fail "expandDefs: wont expand"
        else do
          def <- MaybeT (fromTermDef <$> prtDefOf TermNamespace n)
          let res = SystF.appN def args
          return res
    go _ = fail "expandDefs: not an SystF.App"

{-
-- |Expand the occurences of @n@ in the body of @m@
expandDefIn :: (PirouetteReadDefs m) => Name -> Name -> m ()
expandDefIn n m = pushCtx ("expandDefIn " ++ show n ++ " " ++ show m) $ do
  isRec <- termIsRecursive n -- let's ensure n is not recursive
  if isRec
  then fail "expandDefIn: can't expand recursive term"
  else do
    -- fetch the current definition of n,
    mdefn <- fromTermDef <$> prtDefOf n
    defn  <- maybe (fail "expandDefIn: n not a termdef") return mdefn
    -- fetch the current definition of m and, if its a DFunction, perform the rewrite
    mdefm <- prtDefOf m
    case mdefm of
      DFunction r body ty -> do
        let body' = deshadowBoundNames $ SystF.expandVar (SystF.F $ FreeName n, defn) body
        modifyDef m (const $ Just $ DFunction r body' ty)
      _ -> fail "expandDefIn: m not a termdef"
-}

-- | Simplify /destructor after constructor/ applications. For example,
--
--  > [d/Maybe [c/Just X] N (\ J)] == [J X]
constrDestrId :: (Show meta, Data meta, Typeable meta, PirouetteReadDefs lang m) => TermMeta lang meta -> m (TermMeta lang meta)
constrDestrId = rewriteM (runMaybeT . go)
  where
    go :: (Show meta, PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (TermMeta lang meta)
    go t = do
      UnDestMeta _ tyN _tyArgs x _ret cases excess <- unDest t
      UnConsMeta tyN' _xTyArgs xIdx xArgs <- unCons x
      guard (tyN == tyN')
      let xCase = unsafeIdx "constrDestrId" cases xIdx
      return $ SystF.appN (SystF.appN xCase (map SystF.TermArg xArgs)) excess

-- `chooseHeadCase f tyf [st,INPUT,param] INPUT` creates a term which contains the body of `f`
-- but with a matching on the `INPUT` at the head of it.
-- For instance, if the input type has two constructors `C1` and `C2`, the output is:
--
-- match INPUT#1 with
--   C1 x -> f st#3 (C1 x#0) param#1
--   C2 x y -> f st#4 (c2 x#1 y#0) param#2

chooseHeadCase ::
  (PirouetteReadDefs lang m) =>
  Term lang ->
  Type lang ->
  [String] ->
  String ->
  m (Term lang)
chooseHeadCase t ty args fstArg =
  let argLength = length args
   in let tyOut = snd (SystF.tyFunArgs ty)
       in case elemIndex fstArg args of
            Nothing -> prtError $ PEOther "No argument declared as input"
            Just index ->
              let tyInput = unsafeIdx "chooseHeadCase" (fst $ SystF.tyFunArgs ty) index
               in case nameOf tyInput of
                    Nothing -> prtError $ PEOther "The input is not of a pattern-matchable type"
                    Just tyName -> do
                      dest <- blindDest tyOut <$> prtTypeDefOf tyName
                      let transiAbsInput =
                            SystF.Lam (SystF.Ann $ fromString "DUMMY_ARG") tyInput $
                              SystF.appN t (zipWith transitionArgs args [argLength, argLength - 1 .. 1])
                      let body =
                            subst
                              ( Just transiAbsInput
                                  :< Just (SystF.termPure (SystF.Bound (fromString fstArg) (toInteger $ argLength - 1 - index)))
                                  :< Inc 0
                              )
                              dest
                      constrDestrId body
  where
    nameOf :: Type lang -> Maybe Name
    nameOf (SystF.TyApp (SystF.Free (TySig x)) _) = Just x
    nameOf _ = Nothing

    -- `blindDest out ty` constructs the term
    -- match i#1 with
    --   C1 x0 -> f#0 (C1 x0)
    --   C2 x0 x1 -> f#0 (C2 x0 x1)
    -- where `i` is of type `ty` and `f : ty -> out`
    blindDest :: Type lang -> TypeDef lang -> Term lang
    blindDest tyOut (Datatype _ _ dest cons) =
      SystF.App (SystF.Free (TermSig dest)) $
        SystF.TermArg (SystF.termPure (SystF.Bound (fromString "i") 1)) :
        SystF.TyArg tyOut :
        map (SystF.TermArg . consCase) cons

    consCase :: (Name, Type lang) -> Term lang
    consCase (n, consTy) =
      let (argsTy, _) = SystF.tyFunArgs consTy
       in createNLams "x" argsTy $
            SystF.App
              (SystF.Bound (fromString "f") (toInteger (length argsTy)))
              [SystF.TermArg $ SystF.App (SystF.Free (TermSig n)) (geneXs (length argsTy))]

    -- `createNLams "x" [a,b,c] t` constructs the term
    -- \ (x0 : a) (x1 : b) (x2 : c) -> t
    createNLams :: String -> [Type lang] -> Term lang -> Term lang
    createNLams s tys =
      let go [] _ = id
          go (h : tl) i =
            SystF.Lam (SystF.Ann $ fromString (s ++ show i)) h . go tl (i + 1)
       in go tys (0 :: Int)

    -- `geneXs 3` is the representation of `[x0#2, x1#1, x2#0]`,
    -- which are the arguments expected after a `\x0 x1 x2`.
    geneXs :: Int -> [SystF.Arg ty (Term lang)]
    geneXs n =
      map
        (\i -> SystF.TermArg $ SystF.termPure (SystF.Bound (fromString $ "x" ++ show i) (toInteger $ n - 1 - i)))
        [0 .. n - 1]

    -- Replace the argument "INPUT" by a dummy version of it, which is bound at index 0.
    transitionArgs :: String -> Int -> SystF.Arg ty (Term lang)
    transitionArgs s n
      | s == fstArg = SystF.TermArg $ SystF.termPure (SystF.Bound (fromString "DUMMY_ARG") 0)
      | otherwise = SystF.TermArg $ SystF.termPure (SystF.Bound (fromString s) (toInteger n))

-- | Returns an equivalent /destructor normal-form/ (DNF) term.
--  We say a term is in /destructor normal-form/ when all destructors
--  are pushed to the root of the term. For example, take
--
--  > t = [f [d/Maybe x N (\ J)] a0 a1]
--
--  We return:
--
--  >  [d/Maybe x $(destrNF [f N a0 a1]) (\ $(destrNF [f J a0 a1]))]
--
--  that is, we push the application of f down to the branches of the "case" statement.
destrNF :: forall lang m meta. (Show meta, Data meta, Typeable meta, PirouetteReadDefs lang m) => TermMeta lang meta -> m (TermMeta lang meta)
destrNF = rewriteM (runMaybeT . go)
  where
    -- Returns a term that is a destructor from a list of terms respecting
    -- the invariant that if @splitDest t == Just (xs , d , ys)@, then @t == xs ++ [d] ++ ys@
    splitDest ::
      [ArgMeta lang meta] ->
      MaybeT
        m
        ( TermMeta lang meta,
          ListZipper (ArgMeta lang meta)
        )
    splitDest [] = fail "splitDest: can't split empty list"
    splitDest (a@(SystF.TermArg a2@(SystF.App (SystF.Free (TermSig n)) _)) : ds) =
      (prtIsDest n >> return (a2, ListZipper ([], ds)))
        <|> (splitDest ds <&> second (zipperCons a))
    splitDest (a : ds) = splitDest ds <&> second (zipperCons a)

    go :: TermMeta lang meta -> MaybeT m (TermMeta lang meta)
    go (SystF.App (SystF.Bound _ _) _) = fail "destrNF.go: bound name"
    go (SystF.App (SystF.Free (TermSig fn)) fargs) = do
      -- Try to see if there's at least one destructor in the arguments.
      -- If we find a destructor within the arguments, we can make sure it
      -- is an `App` and has at least one argument (the value being destructed).
      (dest, fargsZ) <- splitDest fargs
      MaybeT $
        case prtIsDest fn of
          MaybeT isDestFn -> do
            mIsDestFn <- isDestFn
            case mIsDestFn of
              Nothing -> runMaybeT $ continue dest fargsZ
              Just _ ->
                if any isTermArg (fst (unListZipper fargsZ))
                  then return Nothing
                  else runMaybeT $ continue dest fargsZ
      where
        isTermArg (SystF.TermArg _) = True
        isTermArg (SystF.TyArg _) = False

        continue dest fargsZ = do
          UnDestMeta dn _ tyArgs x ret cases _ <- unDest dest
          -- Now, we need to push `fn` down the arguments of the destructor, but in doing
          -- so, we need to shift the bound variables depending on how many arguments each
          -- constructor has. Finally, there might be more destructors in fargsZ, which we need to handle,
          -- hence we resurse with the 'onApp' modifier,
          let cases' =
                map
                  ( SystF.preserveLams $ \k ->
                      SystF.App (SystF.Free $ TermSig fn) . flip plug (fmap (SystF.argMap id $ shift k) fargsZ) . SystF.TermArg
                  )
                  cases
          -- TODO: This is still wrong, the destructor now doesn't return something of type `ret`,
          --       but instead, it returns something of whichever type f returns.
          return $
            SystF.App (SystF.Free (TermSig dn)) $
              map SystF.TyArg tyArgs ++ [SystF.TermArg x, SystF.TyArg ret] ++ map SystF.TermArg cases'
    go _ = fail "destrNF.go: not an app"

-- | A 'ListZipper' is a zipper as in one-hole-contexts
newtype ListZipper a = ListZipper {unListZipper :: ([a], [a])}

instance Functor ListZipper where
  fmap f (ListZipper (xs, xs')) = ListZipper (map f xs, map f xs')

plug :: a -> ListZipper a -> [a]
plug a (ListZipper (xs, xs')) = xs ++ [a] ++ xs'

zipperCons :: a -> ListZipper a -> ListZipper a
zipperCons a (ListZipper (xs, xs')) = ListZipper (a : xs, xs')
