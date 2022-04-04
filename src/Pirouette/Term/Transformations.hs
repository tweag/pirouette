{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.Transformations where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad.Except
import Data.Data
import Data.Functor
import Data.Generics.Uniplate.Data
import Data.List (elemIndex, foldl')
import qualified Data.Map as Map
import Data.String (fromString)
import qualified Data.Text as Text
import Language.Pirouette.PlutusIR.Builtins
import Pirouette.Monad
import Pirouette.Monad.Logger
import Pirouette.Monad.Maybe
import Pirouette.Specializer.PIRTransformations
import Pirouette.Specializer.Rewriting
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
removeExcessiveDestArgs = pushCtx "removeExcessiveDestArgs" . rewriteM (runMaybeT . go)
  where
    go :: (Show meta, PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (TermMeta lang meta)
    go t = do
      UnDestMeta n tyN tyArgs x tyReturn cases excess <- unDest t
      if null excess
        then fail "No excessive destr arguments"
        else do
          logTrace $ show n
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
    tyDrop n (SystF.TyFun _ b) = tyDrop (n -1) b
    tyDrop n (SystF.TyAll _ _ t) = tyDrop (n -1) t
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
expandDefs = fmap deshadowBoundNames . pushCtx "expandDefs" . rewriteM (runMaybeT . go)
  where
    go :: Term lang -> MaybeT m (Term lang)
    go (SystF.App (SystF.Free (TermSig n)) args) = do
      isRec <- lift $ termIsRecursive n
      if isRec
        then fail "expandDefs: wont expand"
        else do
          def <- MaybeT (fromTermDef <$> prtDefOf n)
          logTrace ("Expanding: " ++ show n ++ " " ++ show (pretty args) ++ "\n" ++ show (pretty def))
          let res = SystF.appN def args
          logTrace ("Result: " ++ show (pretty res))
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
constrDestrId = pushCtx "constrDestrId" . rewriteM (runMaybeT . go)
  where
    go :: (Show meta, PirouetteReadDefs lang m) => TermMeta lang meta -> MaybeT m (TermMeta lang meta)
    go t = do
      UnDestMeta _ tyN _tyArgs x _ret cases excess <- unDest t
      UnConsMeta tyN' _xTyArgs xIdx xArgs <- unCons x
      guard (tyN == tyN')
      let xCase = unsafeIdx "constrDestrId" cases xIdx
      logTrace $ show tyN
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
            Nothing -> throwError' $ PEOther "No argument declared as input"
            Just index ->
              let tyInput = unsafeIdx "chooseHeadCase" (fst $ SystF.tyFunArgs ty) index
               in case nameOf tyInput of
                    Nothing -> throwError' $ PEOther "The input is not of a pattern-matchable type"
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
        [0 .. n -1]

    -- Replace the argument "INPUT" by a dummy version of it, which is bound at index 0.
    transitionArgs :: String -> Int -> SystF.Arg ty (Term lang)
    transitionArgs s n
      | s == fstArg = SystF.TermArg $ SystF.termPure (SystF.Bound (fromString "DUMMY_ARG") 0)
      | otherwise = SystF.TermArg $ SystF.termPure (SystF.Bound (fromString s) (toInteger n))

-- If a transformation file is declared,
-- then all rewriting rules of the form
-- Name : left-hand side ==> right-hand side
-- are applied in the top to bottom order.

-- TODO: Currently we do simple pattern matching,
-- meaning that the matching substitution cannot contain any bound variables.
-- Ideally, one would like to have matching variables with contexts.
-- For instance, one would like to write something like:
-- BetaRule : [(lam x T a1_[x]) 0] ==> a1_[0]

applyRewRules ::
  (PirouetteReadDefs BuiltinsOfPIR m) =>
  Term BuiltinsOfPIR ->
  m (Term BuiltinsOfPIR)
applyRewRules t = foldM (flip applyOneRule) t (map parseRewRule allRewRules)
  where
    applyOneRule ::
      (PirouetteReadDefs BuiltinsOfPIR m) =>
      RewritingRule (Term BuiltinsOfPIR) (Term BuiltinsOfPIR) ->
      Term BuiltinsOfPIR ->
      m (Term BuiltinsOfPIR)
    applyOneRule RewritingRule { lhs, rhs } tm =
      deshadowBoundNames <$> rewriteM (traverse (`instantiate` rhs) . isInstance lhs) tm

    isInstance :: Term BuiltinsOfPIR -> Term BuiltinsOfPIR -> Maybe (Map.Map String (Arg BuiltinsOfPIR))
    isInstance = isInstanceUnder 0 0

    isInstanceUnder :: Int -> Int -> Term BuiltinsOfPIR -> Term BuiltinsOfPIR -> Maybe (Map.Map String (Arg BuiltinsOfPIR))
    isInstanceUnder nTe _ (SystF.App vL@(SystF.Free (TermSig x)) []) tm =
      case isHole x of
        Nothing ->
          case tm of
            SystF.App vT [] -> isVarInstance vL vT
            _ -> Nothing
        Just i -> Just $ Map.singleton i (SystF.TermArg $ shift (toInteger (- nTe)) t)
    isInstanceUnder nTe nTy (SystF.App vL argsL) (SystF.App vT argsT) =
      foldl' Map.union <$> isVarInstance vL vT <*> zipWithM (isArgInstance nTe nTy) argsL argsT
    isInstanceUnder nTe nTy (SystF.Lam _ tyL tL) (SystF.Lam _ tyT tT) =
      Map.union <$> isInstanceUnder (nTe + 1) nTy tL tT <*> isTyInstance nTy tyL tyT
    isInstanceUnder nTe nTy (SystF.Abs _ _ tL) (SystF.Abs _ _ tT) =
      isInstanceUnder nTe (nTy + 1) tL tT
    isInstanceUnder _nTe _nTy _ _ = Nothing

    isVarInstance :: Var BuiltinsOfPIR -> Var BuiltinsOfPIR -> Maybe (Map.Map String (Arg BuiltinsOfPIR))
    isVarInstance (SystF.Free (TermSig x)) vT =
      case isHole x of
        Nothing ->
          case vT of
            SystF.Free y ->
              if haveSameString (TermSig x) y
                then Just Map.empty
                else Nothing
            _ -> Nothing
        Just i -> Just $ Map.singleton i (SystF.TermArg $ SystF.termPure vT)
    isVarInstance (SystF.Free nL) (SystF.Free nT) =
      if haveSameString nL nT then Just Map.empty else Nothing
    isVarInstance SystF.Bound {} (SystF.Free _) = Nothing
    isVarInstance (SystF.Bound _ i) (SystF.Bound _ j) =
      if i == j then Just Map.empty else Nothing
    isVarInstance _ _ = Nothing

    isTyInstance :: Int -> Type BuiltinsOfPIR -> Type BuiltinsOfPIR -> Maybe (Map.Map String (Arg BuiltinsOfPIR))
    isTyInstance nTy (SystF.TyApp vL@(SystF.Free (TySig x)) []) ty =
      case isHole x of
        Nothing ->
          case ty of
            SystF.TyApp vT [] -> isTyVarInstance vL vT
            _ -> Nothing
        Just i -> Just $ Map.singleton i (SystF.TyArg $ shift (toInteger (- nTy)) ty)
    isTyInstance nTy (SystF.TyApp vL argsL) (SystF.TyApp vT argsT) =
      foldl' Map.union <$> isTyVarInstance vL vT <*> zipWithM (isTyInstance nTy) argsL argsT
    isTyInstance nTy (SystF.TyLam _ _ tyL) (SystF.TyLam _ _ tyT) = isTyInstance (nTy + 1) tyL tyT
    isTyInstance nTy (SystF.TyAll _ _ tyL) (SystF.TyAll _ _ tyT) = isTyInstance (nTy + 1) tyL tyT
    isTyInstance nTy (SystF.TyFun aL bL) (SystF.TyFun aT bT) =
      Map.union <$> isTyInstance nTy aL aT <*> isTyInstance nTy bL bT
    isTyInstance _nTy _ _ = Nothing

    isTyVarInstance :: TyVar BuiltinsOfPIR -> TyVar BuiltinsOfPIR -> Maybe (Map.Map String (Arg BuiltinsOfPIR))
    isTyVarInstance (SystF.Free (TySig x)) vT =
      case isHole x of
        Nothing ->
          case vT of
            SystF.Free y ->
              if tyHaveSameString (TySig x) y
                then Just Map.empty
                else Nothing
            _ -> Nothing
        Just i -> Just $ Map.singleton i (SystF.TyArg $ SystF.tyPure vT)
    isTyVarInstance (SystF.Free nL) (SystF.Free nT) =
      if tyHaveSameString nL nT then Just Map.empty else Nothing
    isTyVarInstance SystF.Bound {} (SystF.Free _) = Nothing
    isTyVarInstance (SystF.Bound _ i) (SystF.Bound _ j) =
      if i == j then Just Map.empty else Nothing
    isTyVarInstance _ _ = Nothing

    isArgInstance :: Int -> Int -> Arg BuiltinsOfPIR -> Arg BuiltinsOfPIR -> Maybe (Map.Map String (Arg BuiltinsOfPIR))
    isArgInstance nTe nTy (SystF.TermArg tL) (SystF.TermArg tT) = isInstanceUnder nTe nTy tL tT
    isArgInstance _ nTy (SystF.TyArg tyL) (SystF.TyArg tyT) = isTyInstance nTy tyL tyT
    isArgInstance _nTe _nTy _ _ = Nothing

    instantiate ::
      (PirouetteReadDefs BuiltinsOfPIR m) =>
      Map.Map String (Arg BuiltinsOfPIR) ->
      Term BuiltinsOfPIR ->
      m (Term BuiltinsOfPIR)
    instantiate = instantiateUnder 0 0

    instantiateUnder ::
      (PirouetteReadDefs BuiltinsOfPIR m) =>
      Int ->
      Int ->
      Map.Map String (Arg BuiltinsOfPIR) ->
      Term BuiltinsOfPIR ->
      m (Term BuiltinsOfPIR)
    instantiateUnder nTe nTy m (SystF.App v@(SystF.Free (TermSig x)) args) = do
      case isHole x of
        Nothing -> SystF.App v <$> mapM (instantiateArg nTe nTy m) args
        Just i ->
          case Map.lookup i m of
            Nothing -> throwError' $ PEOther $ "Variable " ++ show i ++ " appears on the right hand side, but not on the left-hand side."
            Just (SystF.TermArg tm) ->
              SystF.appN (shift (toInteger nTe) tm) <$> mapM (instantiateArg nTe nTy m) args
            Just (SystF.TyArg _) -> throwError' $ PEOther $ "Variable x" ++ show i ++ " is at a term position on the right hand side, but was a type on the left-hand side."
    instantiateUnder nTe nTy m (SystF.App v args) =
      SystF.App v <$> mapM (instantiateArg nTe nTy m) args
    instantiateUnder nTe nTy m (SystF.Lam ann ty tm) =
      SystF.Lam ann <$> instantiateTy nTy m ty <*> instantiateUnder (nTe + 1) nTy m tm
    instantiateUnder nTe nTy m (SystF.Abs ann k tm) =
      SystF.Abs ann k <$> instantiateUnder nTe (nTy + 1) m tm

    instantiateTy ::
      (PirouetteReadDefs BuiltinsOfPIR m) =>
      Int ->
      Map.Map String (Arg BuiltinsOfPIR) ->
      Type BuiltinsOfPIR ->
      m (Type BuiltinsOfPIR)
    instantiateTy nTy m (SystF.TyApp v@(SystF.Free (TySig x)) args) =
      case isHole x of
        Nothing -> SystF.TyApp v <$> mapM (instantiateTy nTy m) args
        Just i ->
          case Map.lookup i m of
            Nothing -> throwError' $ PEOther $ "Variable " ++ show i ++ " appears on the right hand side, but not on the left-hand side."
            Just (SystF.TyArg tm) ->
              SystF.appN (shift (toInteger nTy) tm) <$> mapM (instantiateTy nTy m) args
            Just (SystF.TermArg _) -> throwError' $ PEOther $ "Variable " ++ show i ++ " is at a type position on the right hand side, but was a term on the left-hand side."
    instantiateTy nTy m (SystF.TyApp v args) =
      SystF.TyApp v <$> mapM (instantiateTy nTy m) args
    instantiateTy nTy m (SystF.TyLam ann k ty) =
      SystF.TyLam ann k <$> instantiateTy (nTy + 1) m ty
    instantiateTy nTy m (SystF.TyAll ann k ty) =
      SystF.TyAll ann k <$> instantiateTy (nTy + 1) m ty
    instantiateTy nTy m (SystF.TyFun a b) =
      SystF.TyFun <$> instantiateTy nTy m a <*> instantiateTy nTy m b

    instantiateArg ::
      (PirouetteReadDefs BuiltinsOfPIR m) =>
      Int ->
      Int ->
      Map.Map String (Arg BuiltinsOfPIR) ->
      Arg BuiltinsOfPIR ->
      m (Arg BuiltinsOfPIR)
    instantiateArg nTe nTy m (SystF.TermArg tm) = SystF.TermArg <$> instantiateUnder nTe nTy m tm
    instantiateArg _ nTy m (SystF.TyArg ty) = SystF.TyArg <$> instantiateTy nTy m ty

    isHole :: Name -> Maybe String
    isHole n =
      let x = Text.unpack $ nameString n
       in if length x > 1 && last x == '_' then Just x else Nothing

    haveSameString :: TermBase BuiltinsOfPIR -> TermBase BuiltinsOfPIR -> Bool
    haveSameString (Constant a) (Constant b) = a == b
    haveSameString (Builtin f) (Builtin g) = f == g
    haveSameString Bottom Bottom = True
    haveSameString (TermSig x) (TermSig y) = nameString x == nameString y
    haveSameString _ _ = False

    tyHaveSameString :: TypeBase BuiltinsOfPIR -> TypeBase BuiltinsOfPIR -> Bool
    tyHaveSameString (TyBuiltin f) (TyBuiltin g) = f == g
    tyHaveSameString (TySig x) (TySig y) = nameString x == nameString y
    tyHaveSameString _ _ = False

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
destrNF = pushCtx "destrNF" . rewriteM (runMaybeT . go)
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
          logTrace $ "Pushing " ++ show fn ++ " through " ++ show dn
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
