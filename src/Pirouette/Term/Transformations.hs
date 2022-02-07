{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Term.Transformations where

import           Pirouette.Monad
import           Pirouette.Monad.Logger
import           Pirouette.Monad.Maybe
import           Pirouette.Term.FromPlutusIR
import           Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax.Subst
import           Pirouette.Specializer.Rewriting
import           Pirouette.Specializer.PIRTransformations
import           Pirouette.PlutusIR.Utils

import qualified PlutusIR.Parser    as PIR
import qualified PlutusCore as P
import           Control.Applicative
import           Control.Arrow (first, second, (&&&))
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Reader
import           Data.Data
import           Data.Functor
import           Data.Generics.Uniplate.Data
import           Data.Generics.Uniplate.Operations
import           Data.List (elemIndex, groupBy, transpose, foldl', span, lookup)
import           Data.String (fromString)
import           Data.Maybe (fromMaybe, isJust, fromJust)
import           Prettyprinter hiding (Pretty, pretty)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M

import Debug.Trace (trace)

-- |Put excessive arguments of a a destructor in the branches.
-- Because we have n-ary applications, whenever we translate something like:
--
-- > t = ([[[d/Nat n] (\b -> if b then 0 else 1) (\n b -> if b then n else 0)] True])
--
-- We get:
--
-- > u = [d/Nat n (\b -> if b then 0 else 1) (\n b -> if b then n else 0) True]
--
-- Now, that makes it difficult to swap destructors around since we can only do so
-- when it is in WHNF destructor applications (which forbids over-application).
-- Moreover, it makes the code larger and more difficult to read.
--
-- Hence, calling 'removeExcessiveDestArgs u' will return:
--
-- > v = [d/Nat n (if b then 0 else 1)[b := True] (\n -> if b then n else 0)[b := True]]
-- > v = [d/Nat n 0 (\n -> n)]
--
-- Since the second constructor of Nat is Succ :: Nat -> Nat, one does not want to
-- simply apply (\n b -> if b then n else 0) to True, since the first abstraction
-- corresponds to the argument of Succ.
--
-- Whenever a constructor has no arguments, its destruction in PlutusIR is done using
-- a function which takes an argument of type `Unit`, like:
--
-- > t = ([[[d/Bool x] (\thunk -> T) (\thunk -> F)] Unit])
--
-- We get:
--
-- > u = [d/Bool x (\thunk -> T) (\thunk -> F) Unit]
-- Because PlutusIR is meant to be executed in a strict fashion, these thunks are there
-- to prevent evaluation. For us, it really doesn't matter since we will symbolically evaluate it.
--
-- Hence, calling 'removeExcessiveDestArgs u' will return:
--
-- > v = [d/Bool x T[thunk := Unit] F[thunk := Unit]]
-- Generally v = [d/Bool T F] since `thunk` has no reason to appear in `T` and `F`.
--
removeExcessiveDestArgs :: (Data meta, Typeable meta, PirouetteReadDefs lang m) => PrtTermMeta lang meta -> m (PrtTermMeta lang meta)
removeExcessiveDestArgs = pushCtx "removeExcessiveDestArgs" . rewriteM (runMaybeT . go)
  where
    go :: (PirouetteReadDefs lang m) => PrtTermMeta lang meta -> MaybeT m (PrtTermMeta lang meta)
    go t = do
      UnDestMeta n tyN tyArgs x tyReturn cases excess <- unDest t
      if null excess
      then fail "No excessive destr arguments"
      else do
        logTrace $ show n
        Datatype _ _ _ cons <- lift (prtTypeDefOf tyN)
        let cons' = map (second prtTypeToMeta) cons
        return $
          R.App (R.F $ FreeName n) $
            map R.TyArg tyArgs
              ++ [R.Arg x, R.TyArg $ tyDrop (length excess) tyReturn]
              ++ zipWith (\(_,cty) t -> R.Arg $ appExcessive excess cty t) cons' cases

    -- Receives the excessive arguments, the type of the constructor whose case we're on and
    -- the term defining the value at this constructor's case.
    appExcessive :: [PrtArgMeta lang meta] -> PrtTypeMeta lang meta -> PrtTermMeta lang meta -> PrtTermMeta lang meta
    appExcessive l (R.TyFun a b) (R.Lam n ty t) =
      R.Lam n ty (appExcessive (map (R.argMap id (shift 1)) l) b t) -- `a` and `ty` are equal, up to substitution of variables in the type of the constructors.
    appExcessive l (R.TyFun a b) _              =
       error "Ill-typed program! Number of lambdas in case-branch must be bigger than constructor arity"
    appExcessive l _             t              =
       R.appN t l

    tyDrop :: Int -> PrtTypeMeta lang meta -> PrtTypeMeta lang meta
    tyDrop 0 t               = t
    tyDrop n (R.TyFun a b)   = tyDrop (n-1) b
    tyDrop n (R.TyAll _ _ t) = tyDrop (n-1) t
    tyDrop n t               = error "Ill-typed program: not enough type parameters to drop"

-- |Because TLA+ really doesn't allow for shadowed bound names, we need to rename them
-- after performing any sort of inlining.
deshadowBoundNames :: PrtTerm lang -> PrtTerm lang
deshadowBoundNames = deshadowBoundNamesWithForbiddenNames []


deshadowBoundNamesWithForbiddenNames :: [Name] -> PrtTerm lang -> PrtTerm lang
deshadowBoundNamesWithForbiddenNames = go []
  where
    -- @newAnnFrom ns n@ returns a fresh name similar to @n@ given a list of declared names @ns@.
    -- it does so by incrementing the 'nameUnique' part of 'n'. Instead of incrementing one-by-one,
    -- we increment by i to hopefully require less iterations to find a fresh name.
    newAnnFrom :: [Name] -> [Name] -> Name -> Name
    newAnnFrom anns forbidden a =
      case a `elemIndex` (anns ++ forbidden) of
        Nothing -> a
        Just i  -> newAnnFrom anns forbidden (a { nameUnique = Just $ maybe i ((+i) . (+1)) (nameUnique a) })

    go bvs forbidden (R.Lam (R.Ann ann) ty t)
      = let ann' = newAnnFrom bvs forbidden ann
         in R.Lam (R.Ann ann') ty (go (ann' : bvs) forbidden t)

    go bvs forbidden (R.Abs a ki t) = R.Abs a ki (go bvs forbidden t)
    go bvs forbidden(R.App n args) =
      let args' = map (R.argMap id (go bvs forbidden)) args
          n' =
            case n of
              R.B x i ->
                if fromInteger i >= length bvs
                then n
                else
                  R.B (R.Ann (unsafeIdx "deshadowBoundNames" bvs $ fromInteger i)) i
              _       -> n
      in R.App n' args'

-- |Expand all non-recursive definitions
expandDefs :: forall lang m . (PirouetteReadDefs lang m, Pretty (Constants lang), Pretty (BuiltinTerms lang) , Pretty (BuiltinTypes lang))
           => PrtTerm lang -> m (PrtTerm lang)
expandDefs = fmap deshadowBoundNames . pushCtx "expandDefs" . rewriteM (runMaybeT . go)
  where
    go :: PrtTerm lang -> MaybeT m (PrtTerm lang)
    go (R.App (R.F (FreeName n)) args) = do
      isRec <- lift $ termIsRecursive n
      if isRec
      then fail "expandDefs: wont expand"
      else do
       def <- MaybeT (fromTermDef <$> prtDefOf n)
       logTrace ("Expanding: " ++ show n ++ " " ++ show (pretty args) ++ "\n" ++ show (pretty def))
       let res = R.appN def args
       logTrace ("Result: " ++ show (pretty res))
       return res
    go _ = fail "expandDefs: not an R.App"

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
        let body' = deshadowBoundNames $ R.expandVar (R.F $ FreeName n, defn) body
        modifyDef m (const $ Just $ DFunction r body' ty)
      _ -> fail "expandDefIn: m not a termdef"
-}

-- |Simplify /destructor after constructor/ applications. For example,
--
-- > [d/Maybe [c/Just X] N (\ J)] == [J X]
--
constrDestrId :: (Data meta, Typeable meta, PirouetteReadDefs lang m) => PrtTermMeta lang meta -> m (PrtTermMeta lang meta)
constrDestrId = pushCtx "constrDestrId" . rewriteM (runMaybeT . go)
  where
    go :: (PirouetteReadDefs lang m) => PrtTermMeta lang meta -> MaybeT m (PrtTermMeta lang meta)
    go t = do
      UnDestMeta _ tyN tyArgs x ret cases excess <- unDest t
      UnConsMeta tyN' xTyArgs xIdx xArgs <- unCons x
      guard (tyN == tyN')
      let xCase          = unsafeIdx "constrDestrId" cases xIdx
      logTrace $ show tyN
      return $ R.appN (R.appN xCase (map R.Arg xArgs)) excess

-- `chooseHeadCase f tyf [st,INPUT,param] INPUT` creates a term which contains the body of `f`
-- but with a matching on the `INPUT` at the head of it.
-- For instance, if the input type has two constructors `C1` and `C2`, the output is:
--
-- match INPUT#1 with
--   C1 x -> f st#3 (C1 x#0) param#1
--   C2 x y -> f st#4 (c2 x#1 y#0) param#2

chooseHeadCase :: (PirouetteReadDefs lang m)
               => PrtTerm lang -> PrtType lang -> [String] -> String -> m (PrtTerm lang)
chooseHeadCase t ty args fstArg =
  let argLength = length args in
  let tyOut = snd (R.tyFunArgs ty) in
  case elemIndex fstArg args of
    Nothing -> throwError' $ PEOther "No argument declared as input"
    Just index ->
      let tyInput = unsafeIdx "chooseHeadCase" (fst $ R.tyFunArgs ty) index in
      case nameOf tyInput of
        Nothing -> throwError' $ PEOther "The input is not of a pattern-matchable type"
        Just tyName -> do
          dest <- blindDest tyOut <$> prtTypeDefOf tyName
          let transiAbsInput = R.Lam (R.Ann $ fromString "DUMMY_ARG") tyInput $
                R.appN t (zipWith transitionArgs args [argLength, argLength - 1 .. 1])
          let body = subst
                (  Just transiAbsInput
                :< Just (R.termPure (R.B (fromString fstArg) (toInteger $ argLength - 1 - index)))
                :< Inc 0
                )
                dest
          constrDestrId body

  where
    nameOf :: PrtType lang -> Maybe Name
    nameOf (R.TyApp (R.F (TyFree x)) _) = Just x
    nameOf _ = Nothing

    -- `blindDest out ty` constructs the term
    -- match i#1 with
    --   C1 x0 -> f#0 (C1 x0)
    --   C2 x0 x1 -> f#0 (C2 x0 x1)
    -- where `i` is of type `ty` and `f : ty -> out`
    blindDest :: PrtType lang -> PrtTypeDef lang -> PrtTerm lang
    blindDest tyOut (Datatype _ _ dest cons) =
      R.App (R.F (FreeName dest)) $
        R.Arg (R.termPure (R.B (fromString "i") 1)) :
        R.TyArg tyOut :
        map (R.Arg . consCase) cons

    consCase :: (Name, PrtType lang) -> PrtTerm lang
    consCase (n, ty) =
      let (argsTy,_) = R.tyFunArgs ty in
      createNLams "x" argsTy $
        R.App
          (R.B (fromString "f") (toInteger (length argsTy)))
          [R.Arg $ R.App (R.F (FreeName n)) (geneXs (length argsTy))]

    -- `createNLams "x" [a,b,c] t` constructs the term
    -- \ (x0 : a) (x1 : b) (x2 : c) -> t
    createNLams :: String -> [PrtType lang] -> PrtTerm lang -> PrtTerm lang
    createNLams s tys =
      let go [] _ = id
          go (h:tl) i =
            R.Lam (R.Ann $ fromString (s ++ show i)) h . go tl (i + 1)
      in
      go tys 0

    -- `geneXs 3` is the representation of `[x0#2, x1#1, x2#0]`,
    -- which are the arguments expected after a `\x0 x1 x2`.
    geneXs :: Int -> [R.Arg ty (PrtTerm lang)]
    geneXs n =
      map
        (\i -> R.Arg $ R.termPure (R.B (fromString $ "x" ++ show i) (toInteger $ n - 1 - i)))
        [0 .. n-1]

    -- Replace the argument "INPUT" by a dummy version of it, which is bound at index 0.
    transitionArgs :: String -> Int -> R.Arg ty (PrtTerm lang)
    transitionArgs s n
      | s == fstArg = R.Arg $ R.termPure (R.B (fromString "DUMMY_ARG") 0)
      | otherwise   = R.Arg $ R.termPure (R.B (fromString s) (toInteger n))

-- If a transformation file is declared,
-- then all rewriting rules of the form
-- Name : left-hand side ==> right-hand side
-- are applied in the top to bottom order.

-- TODO: Currently we do simple pattern matching,
-- meaning that the matching substitution cannot contain any bound variables.
-- Ideally, one would like to have matching variables with contexts.
-- For instance, one would like to write something like:
-- BetaRule : [(lam x T a1_[x]) 0] ==> a1_[0]

applyRewRules :: (PirouetteReadDefs PlutusIR m)
              => PirTerm -> m PirTerm
applyRewRules t = foldM (flip applyOneRule) t (map parseRewRule allRewRules)

  where

    applyOneRule :: (PirouetteReadDefs PlutusIR m)
                 => RewritingRule PirTerm PirTerm -> PirTerm -> m PirTerm
    applyOneRule (RewritingRule name lhs rhs) t =
      deshadowBoundNames <$> rewriteM (traverse (`instantiate` rhs) . isInstance lhs) t

    isInstance :: PirTerm  -> PirTerm -> Maybe (M.Map String (PrtArg PlutusIR))
    isInstance = isInstanceUnder 0 0

    isInstanceUnder :: Int -> Int -> PirTerm  -> PirTerm -> Maybe (M.Map String (PrtArg PlutusIR))
    isInstanceUnder nTe nTy (R.App vL@(R.F (FreeName x)) []) t =
      case isHole x of
        Nothing ->
          case t of
            R.App vT [] -> isVarInstance vL vT
            _ -> Nothing
        Just i -> Just $ M.singleton i (R.Arg $ shift (toInteger (- nTe)) t)
    isInstanceUnder nTe nTy  (R.App vL argsL) (R.App vT argsT) =
      foldl' M.union <$> isVarInstance vL vT <*> zipWithM (isArgInstance nTe nTy) argsL argsT
    isInstanceUnder nTe nTy  (R.Lam _ tyL tL) (R.Lam _ tyT tT) =
      M.union <$> isInstanceUnder (nTe + 1) nTy tL tT <*> isTyInstance nTy tyL tyT
    isInstanceUnder nTe nTy (R.Abs _ _ tL) (R.Abs _ _ tT) =
      isInstanceUnder nTe (nTy + 1) tL tT
    isInstanceUnder nTe nTy _ _ = Nothing

    isVarInstance :: PrtVar PlutusIR -> PrtVar PlutusIR -> Maybe (M.Map String (PrtArg PlutusIR))
    isVarInstance vL@(R.F (FreeName x)) vT =
      case isHole x of
        Nothing ->
          case vT of
            R.F y ->
              if haveSameString (FreeName x) y
              then Just M.empty
              else Nothing
            _ -> Nothing
        Just i -> Just $ M.singleton i (R.Arg $ R.termPure vT)
    isVarInstance (R.F nL) (R.F nT) =
      if haveSameString nL nT then Just M.empty else Nothing
    isVarInstance (R.B _ i) (R.F _) = Nothing
    isVarInstance (R.B _ i) (R.B _ j) =
      if i == j then Just M.empty else Nothing
    isVarInstance _ _ = Nothing

    isTyInstance :: Int -> PirType -> PirType -> Maybe (M.Map String (PrtArg PlutusIR))
    isTyInstance nTy (R.TyApp vL@(R.F (TyFree x)) []) ty =
      case isHole x of
        Nothing ->
          case ty of
            R.TyApp vT [] -> isTyVarInstance vL vT
            _ -> Nothing
        Just i -> Just $ M.singleton i (R.TyArg $ shift (toInteger (- nTy)) ty)
    isTyInstance nTy (R.TyApp vL argsL) (R.TyApp vT argsT) =
      foldl' M.union <$> isTyVarInstance vL vT <*> zipWithM (isTyInstance nTy) argsL argsT
    isTyInstance nTy (R.TyLam _ _ tyL) (R.TyLam _ _ tyT) = isTyInstance (nTy + 1) tyL tyT
    isTyInstance nTy (R.TyAll _ _ tyL) (R.TyAll _ _ tyT) = isTyInstance (nTy + 1) tyL tyT
    isTyInstance nTy (R.TyFun aL bL) (R.TyFun aT bT) =
      M.union <$> isTyInstance nTy aL aT <*> isTyInstance nTy bL bT
    isTyInstance nTy _ _ = Nothing

    isTyVarInstance :: PrtTyVar PlutusIR -> PrtTyVar PlutusIR -> Maybe (M.Map String (PrtArg PlutusIR))
    isTyVarInstance vL@(R.F (TyFree x)) vT =
      case isHole x of
        Nothing ->
          case vT of
            R.F y ->
              if tyHaveSameString (TyFree x) y
              then Just M.empty
              else Nothing
            _ -> Nothing
        Just i -> Just $ M.singleton i (R.TyArg $ R.tyPure vT)
    isTyVarInstance (R.F nL) (R.F nT) =
      if tyHaveSameString nL nT then Just M.empty else Nothing
    isTyVarInstance (R.B _ i) (R.F _) = Nothing
    isTyVarInstance (R.B _ i) (R.B _ j) =
      if i == j  then Just M.empty else Nothing
    isTyVarInstance _ _ = Nothing

    isArgInstance :: Int -> Int -> PrtArg PlutusIR -> PrtArg PlutusIR -> Maybe (M.Map String (PrtArg PlutusIR))
    isArgInstance nTe nTy (R.Arg tL) (R.Arg tT) = isInstanceUnder nTe nTy tL tT
    isArgInstance nTe nTy (R.TyArg tyL) (R.TyArg tyT) = isTyInstance nTy tyL tyT
    isArgInstance nTe nTy _ _ = Nothing

    instantiate :: (PirouetteReadDefs PlutusIR m)
                => M.Map String (PrtArg PlutusIR) -> PrtTerm PlutusIR -> m (PrtTerm PlutusIR)
    instantiate = instantiateUnder 0 0

    instantiateUnder :: (PirouetteReadDefs PlutusIR m)
                => Int -> Int -> M.Map String (PrtArg PlutusIR) -> PrtTerm PlutusIR -> m (PrtTerm PlutusIR)
    instantiateUnder nTe nTy m tt@(R.App v@(R.F (FreeName x)) args) =do
      case isHole x of
        Nothing -> R.App v <$> mapM (instantiateArg nTe nTy m) args
        Just i ->
          case M.lookup i m of
            Nothing -> throwError' $ PEOther $ "Variable " ++ show i ++ " appears on the right hand side, but not on the left-hand side."
            Just (R.Arg t) ->
              R.appN (shift (toInteger nTe) t) <$> mapM (instantiateArg nTe nTy m) args
            Just (R.TyArg ty) -> throwError' $ PEOther $ "Variable x" ++ show i ++ " is at a term position on the right hand side, but was a type on the left-hand side."
    instantiateUnder nTe nTy m (R.App v args) =
      R.App v <$> mapM (instantiateArg nTe nTy m) args
    instantiateUnder nTe nTy m (R.Lam ann ty t) =
      R.Lam ann <$> instantiateTy nTy m ty <*> instantiateUnder (nTe + 1) nTy m t
    instantiateUnder nTe nTy m (R.Abs ann k t) =
      R.Abs ann k <$> instantiateUnder nTe (nTy + 1) m t

    instantiateTy :: (PirouetteReadDefs PlutusIR m)
                  => Int -> M.Map String (PrtArg PlutusIR) -> PrtType PlutusIR -> m (PrtType PlutusIR)
    instantiateTy nTy m (R.TyApp v@(R.F (TyFree x)) args) =
      case isHole x of
        Nothing -> R.TyApp v <$> mapM (instantiateTy nTy m) args
        Just i ->
          case M.lookup i m of
            Nothing -> throwError' $ PEOther $ "Variable " ++ show i ++ " appears on the right hand side, but not on the left-hand side."
            Just (R.TyArg t) ->
              R.appN (shift (toInteger nTy) t) <$> mapM (instantiateTy nTy m) args
            Just (R.Arg ty) -> throwError' $ PEOther $ "Variable " ++ show i ++ " is at a type position on the right hand side, but was a term on the left-hand side."
    instantiateTy nTy m (R.TyApp v args) =
      R.TyApp v <$> mapM (instantiateTy nTy m) args
    instantiateTy nTy m (R.TyLam ann k ty) =
      R.TyLam ann k <$> instantiateTy (nTy + 1) m ty
    instantiateTy nTy m (R.TyAll ann k ty) =
      R.TyAll ann k <$> instantiateTy (nTy + 1) m ty
    instantiateTy nTy m (R.TyFun a b) =
      R.TyFun <$> instantiateTy nTy m a <*> instantiateTy nTy m b

    instantiateArg :: (PirouetteReadDefs PlutusIR m)
                   => Int -> Int -> M.Map String (PrtArg PlutusIR) -> PrtArg PlutusIR -> m (PrtArg PlutusIR)
    instantiateArg nTe nTy m (R.Arg t) = R.Arg <$> instantiateUnder nTe nTy m t
    instantiateArg nTe nTy m (R.TyArg ty) = R.TyArg <$> instantiateTy nTy m ty

    isHole :: Name -> Maybe String
    isHole n =
      let x = T.unpack $ nameString n in
      if length x > 1 && last x == '_' then Just x else Nothing

    haveSameString :: TermBase PlutusIR Name -> TermBase PlutusIR Name -> Bool
    haveSameString (Constant a) (Constant b) = a == b
    haveSameString (Builtin f) (Builtin g) = f == g
    haveSameString Bottom Bottom = True
    haveSameString (FreeName x) (FreeName y) = nameString x == nameString y
    haveSameString _ _ = False

    tyHaveSameString :: TypeBase PlutusIR Name -> TypeBase PlutusIR Name -> Bool
    tyHaveSameString (TyBuiltin f) (TyBuiltin g) = f == g
    tyHaveSameString (TyFree x) (TyFree y) = nameString x == nameString y
    tyHaveSameString _ _ = False

-- |Returns an equivalent /destructor normal-form/ (DNF) term.
-- We say a term is in /destructor normal-form/ when all destructors
-- are pushed to the root of the term. For example, take
--
-- > t = [f [d/Maybe x N (\ J)] a0 a1]
--
-- We return:
--
-- >  [d/Maybe x $(destrNF [f N a0 a1]) (\ $(destrNF [f J a0 a1]))]
--
-- that is, we push the application of f down to the branches of the "case" statement.

destrNF :: forall lang m meta . (Data meta, Typeable meta, PirouetteReadDefs lang m) => PrtTermMeta lang meta -> m (PrtTermMeta lang meta)
destrNF = pushCtx "destrNF" . rewriteM (runMaybeT . go)
  where
    onApp :: (PrtVarMeta lang meta -> [PrtArgMeta lang meta] -> MaybeT m (PrtTermMeta lang meta))
          -> PrtTermMeta lang meta -> m (PrtTermMeta lang meta)
    onApp f t@(R.App n args) = fromMaybe t <$> runMaybeT (f n args)
    onApp _ t                = return t

    -- Returns a term that is a destructor from a list of terms respecting
    -- the invariant that if @splitDest t == Just (xs , d , ys)@, then @t == xs ++ [d] ++ ys@
    splitDest :: [PrtArgMeta lang meta]
              -> MaybeT m ( PrtTermMeta lang meta
                          , ListZipper (PrtArgMeta lang meta))
    splitDest [] = fail "splitDest: can't split empty list"
    splitDest (a@(R.Arg a2@(R.App (R.F (FreeName n)) args)) : ds) =
          (prtIsDest n >> return (a2, ListZipper ([], ds)))
      <|> (splitDest ds <&> second (zipperCons a))
    splitDest (a : ds) = splitDest ds <&> second (zipperCons a)

    go :: PrtTermMeta lang meta -> MaybeT m (PrtTermMeta lang meta)
    go (R.App (R.B _ _)           fargs) = fail "destrNF.go: bound name"
    go (R.App (R.F (FreeName fn)) fargs) = do
      -- Try to see if there's at least one destructor in the arguments.
      -- If we find a destructor within the arguments, we can make sure it
      -- is an `App` and has at least one argument, the value being eliminated.
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
        isTermArg (R.Arg _) = True
        isTermArg (R.TyArg _) = False

        continue dest fargsZ= do
          UnDestMeta dn tyN tyArgs x ret cases excess <- unDest dest
          -- Now, we need to push `fn` down the arguments of the destructor, but in doing
          -- so, we need to shift the bound variables depending on how many arguments each
          -- constructor has. Finally, there might be more destructors in fargsZ, which we need to handle,
          -- hence we resurse with the 'onApp' modifier,
          let cases' = map (R.preserveLams $ \k
                              -> R.App (R.F $ FreeName fn) . flip plug (fmap (R.argMap id $ shift k) fargsZ) . R.Arg) cases
          -- TODO: This is still wrong, the destructor now doesn't return something of type `ret`,
          --       but instead, it returns something of whichever type f returns.
          logTrace $ "Pushing " ++ show fn ++ " through " ++ show dn
          return $ R.App (R.F (FreeName dn))
                $ map R.TyArg tyArgs ++ [R.Arg x, R.TyArg ret] ++ map R.Arg cases'
    go _ = fail "destrNF.go: not an app"

-- |A 'ListZipper' is a zipper as in one-hole-contexts
newtype ListZipper a = ListZipper { unListZipper :: ([a], [a]) }

instance Functor ListZipper where
  fmap f (ListZipper (xs, xs')) = ListZipper (map f xs, map f xs')

plug :: a -> ListZipper a -> [a]
plug a (ListZipper (xs, xs')) = xs ++ [a] ++ xs'

zipperCons :: a -> ListZipper a -> ListZipper a
zipperCons a (ListZipper (xs, xs')) = ListZipper (a:xs, xs')
