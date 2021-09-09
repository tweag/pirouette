{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiWayIf #-}

module Pirouette.Term.Transformations where

import           Pirouette.Monad
import           Pirouette.Monad.Logger
import           Pirouette.Monad.Maybe
import           Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax.Subst
import           Pirouette.PlutusIR.Utils

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
import           Data.Maybe (fromMaybe, isJust)
import           Data.Text.Prettyprint.Doc hiding (pretty)
import qualified Data.Text as T
import qualified Data.Map as M

-- * Monomorphic Transformations

-- |Removes superfluous Bool-match. For example,
--
-- > [b/ifThenElse [b/greaterThanEqualsInteger m n] c/True/Bool c/False/Bool]
--
-- Could be simply:
--
-- > [b/greaterThanEqualsInteger m n]
--
-- WARNING: Before specializing plutus booleans to TLA booleans, this transformation
-- can break things. In the example above, @b/greaterThanEqualsInteger@ returns a plutus builtin boolean,
-- whereas the @ifThenElse@ is returning an element of a @(datatypedecl ... Bool)@.
--
etaIfThenElse :: (MonadPirouette m) => PrtTerm -> m PrtTerm
etaIfThenElse = pushCtx "etaIfThenElse" . transformM go
  where
    go r@(R.App (R.F n) [R.TyArg _, R.Arg x, R.Arg t, R.Arg f]) = do
      pt <- termIsBoolVal True t
      pf <- termIsBoolVal False f
      if nameIsITE n && pt && pf
      then logTrace mempty >> return x
      else return r
    go r = return r

-- * Polymorphic Transformations

-- |Specialize @cfoldableNil_cfoldMap@ applied to the disjunctive bool and endofunction monoids
cfoldmapSpecialize :: forall m . (MonadPirouette m) => PrtTerm -> m PrtTerm
cfoldmapSpecialize = fmap deshadowBoundNames . pushCtx "cfoldmapSpecialize" . rewriteM (runMaybeT . go)
  where
    isCfoldmap :: (Monad t) => PrtTerm -> MaybeT t (PrtType, PrtType, [PrtTerm])
    isCfoldmap (R.App (R.F (FreeName n)) (R.TyArg m : R.TyArg a : args)) = do
      guard ("fFoldableNil_cfoldMap" `T.isPrefixOf` nameString n)
      args' <- mapM (wrapMaybe . R.fromArg) args
      return (m , a , args')
    isCfoldmap _ = fail "not cfoldmap"

    go :: PrtTerm -> MaybeT m PrtTerm
    go t = do
      (m, a, args) <- isCfoldmap t
      tyIsBool <- lift $ typeIsBool m
      if tyIsBool
      then do
        res <- goBool m a args
        logDebug ("Specializing: " ++ renderSingleLineStr (pretty t))
        logDebug ("  for: " ++ renderSingleLineStr (pretty res))
        return res
      else case m of
        R.TyFun t u | t == u -> goEndo t a args
        _ -> logWarn ("Can't specialize for " ++ renderSingleLineStr (pretty m))
          >> fail ""

    -- foldr_135 (all a_136 (type) (all b_137 (type) (fun (fun a_136 (fun b_137 b_137)) (fun b_137 (fun [List_29 a_136] b_137)))))

    -- fFoldableNil_cfoldMap_200 (all m_201 (type) (all a_202 (type) (fun [Monoid_130 m_201] (fun (fun a_202 m_201) (fun [List_29 a_202] m_201)))))

    goBool :: PrtType -> PrtType -> [PrtTerm] -> MaybeT m PrtTerm
    goBool m a [mon,f,xs] = do
      foldrName <- lift $ nameForPrefix "foldr"
      boolMatch <- lift $ nameForPrefix "Bool_match"
      true      <- lift $ nameForPrefix "True"
      false     <- lift $ nameForPrefix "False"
      let annA = R.Ann "a"
          annB = R.Ann "b"
          -- gene = \ a b -> f a || b
          gene = R.Lam annA a $ R.Lam annB m $ R.App (R.F $ FreeName boolMatch)
                 [ R.Arg (R.app (shift 2 f) (R.Arg $ R.App (R.B annA 1) []))
                 , R.TyArg m
                 , R.Arg (R.App (R.F $ FreeName true) [])
                 , R.Arg (R.App (R.B annB 0) [])
                 ]
          zero = R.App (R.F $ FreeName false) []
      return $ R.App (R.F $ FreeName foldrName) [R.TyArg a, R.TyArg m, R.Arg gene, R.Arg zero, R.Arg xs]

    goEndo :: PrtType -> PrtType -> [PrtTerm] -> MaybeT m PrtTerm
    goEndo m a [mon,f,xs,k] = do
      foldrName <- lift $ nameForPrefix "foldr"
      let annA = R.Ann "a"
          annB = R.Ann "b"
          -- gene = \ a b -> f a b
          gene = R.Lam annA a $ R.Lam annB m $ R.appN (shift 2 f)
                 [ R.Arg (R.App (R.B annA 1) [])
                 , R.Arg (R.App (R.B annB 0) [])
                 ]
       in return $ R.App (R.F $ FreeName foldrName) [R.TyArg a, R.TyArg m, R.Arg gene, R.Arg k, R.Arg xs]



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
removeExcessiveDestArgs :: (MonadPirouette m) => PrtTerm -> m PrtTerm
removeExcessiveDestArgs = pushCtx "removeExcessiveDestArgs" . rewriteM (runMaybeT . go)
  where
    go :: (MonadPirouette m) => PrtTerm -> MaybeT m PrtTerm
    go t = do
      (n, tyN, tyArgs, x, tyReturn, cases, excess) <- unDest t
      if null excess
      then fail "No excessive destr arguments"
      else do
        logTrace $ show n
        Datatype _ _ _ cons <- lift (typeDefOf tyN)
        return $
          R.App (R.F $ FreeName n) $
            map R.TyArg tyArgs
              ++ [R.Arg x, R.TyArg $ tyDrop (length excess) tyReturn]
              ++ zipWith (\(_,cty) t -> R.Arg $ appExcessive excess cty t) cons cases

    -- Receives the excessive arguments, the type of the constructor whose case we're on and
    -- the term defining the value at this constructor's case.
    appExcessive :: [R.Arg PrtType PrtTerm] -> Type Name -> PrtTerm -> PrtTerm
    appExcessive l (R.TyFun a b) (R.Lam n ty t) =
      R.Lam n ty (appExcessive (map (R.argMap id (shift 1)) l) b t) -- `a` and `ty` are equal, up to substitution of variables in the type of the constructors.
    appExcessive l (R.TyFun a b) _              =
       error "Ill-typed program! Number of lambdas in case-branch must be bigger than constructor arity"
    appExcessive l _             t              =
       R.appN t l

    tyDrop :: Int -> PrtType -> PrtType
    tyDrop 0 t               = t
    tyDrop n (R.TyFun a b)   = tyDrop (n-1) b
    tyDrop n (R.TyAll _ _ t) = tyDrop (n-1) t
    tyDrop n t               = error "Ill-typed program: not enough type parameters to drop"

-- |Because TLA+ really doesn't allow for shadowed bound names, we need to rename them
-- after performing any sort of inlining.
deshadowBoundNames :: PrtTerm -> PrtTerm
deshadowBoundNames = go []
  where
    -- @newAnnFrom ns n@ returns a fresh name similar to @n@ given a list of declared names @ns@.
    -- it does so by incrementing the 'nameUnique' part of 'n'. Instead of incrementing one-by-one,
    -- we increment by i to hopefully require less iterations to find a fresh name.
    newAnnFrom :: [Name] -> Name -> Name
    newAnnFrom anns a =
      case a `elemIndex` anns of
        Nothing -> a
        Just i  -> newAnnFrom anns (a { nameUnique = Just $ maybe i ((+i) . (+1)) (nameUnique a) })

    go bvs (R.Lam (R.Ann ann) ty t)
      = let ann' = newAnnFrom bvs ann
         in R.Lam (R.Ann ann') ty (go (ann' : bvs) t)

    go bvs (R.Abs a ki t) = R.Abs a ki (go bvs t)
    go bvs (R.App n args) =
      let args' = map (R.argMap id (go bvs)) args
          n' = case n of
                 R.B _ i -> R.B (R.Ann (bvs !! fromInteger i)) i
                 _       -> n
       in R.App n' args'

-- |Expand all non-recursive definitions
expandDefs :: (MonadPirouette m) => PrtTerm -> m PrtTerm
expandDefs = fmap deshadowBoundNames . pushCtx "expandDefs" . rewriteM (runMaybeT . go)
  where
    go :: (MonadPirouette m) => PrtTerm -> MaybeT m PrtTerm
    go (R.App (R.F (FreeName n)) args) = do
      isRec <- lift $ termIsRecursive n
      if isRec
      then fail "expandDefs: wont expand"
      else do
       def <- MaybeT (fromTermDef <$> defOf n)
       logTrace ("Expanding: " ++ show n ++ " " ++ show (pretty args) ++ "\n" ++ show (pretty def))
       let res = R.appN def args
       logTrace ("Result: " ++ show (pretty res))
       return res
    go _ = fail "expandDefs: not an R.App"

-- |Expand the occurences of @n@ in the body of @m@
expandDefIn :: (MonadPirouette m) => Name -> Name -> m ()
expandDefIn n m = pushCtx ("expandDefIn " ++ show n ++ " " ++ show m) $ do
  isRec <- termIsRecursive n -- let's ensure n is not recursive
  if isRec
  then fail "expandDefIn: can't expand recursive term"
  else do
    -- fetch the current definition of n,
    mdefn <- fromTermDef <$> defOf n
    defn  <- maybe (fail "expandDefIn: n not a termdef") return mdefn
    -- fetch the current definition of m and, if its a DFunction, perform the rewrite
    mdefm <- defOf m
    case mdefm of
      DFunction r body ty -> do
        let body' = deshadowBoundNames $ R.expandVar (R.F $ FreeName n, defn) body
        modifyDef m (const $ Just $ DFunction r body' ty)
      _ -> fail "expandDefIn: m not a termdef"

-- |Simplify /destructor after constructor/ applications. For example,
--
-- > [d/Maybe [c/Just X] N (\ J)] == [J X]
--
constrDestrId :: (MonadPirouette m) => PrtTerm -> m PrtTerm
constrDestrId = pushCtx "constrDestrId" . rewriteM (runMaybeT . go)
  where
    go :: (MonadPirouette m) => PrtTerm -> MaybeT m PrtTerm
    go t = do
      (_, tyN, tyArgs, x, ret, cases, excess) <- unDest t
      (tyN', xTyArgs, xIdx, xArgs) <- unCons x
      guard (tyN == tyN')
      let xCase          = cases !! xIdx
      logTrace $ show tyN
      return $ R.appN (R.appN xCase (map R.Arg xArgs)) excess

-- `chooseHeadCase f tyf [st,INPUT,param] INPUT` creates a term which contains the body of `f`
-- but with a matching on the `INPUT` at the head of it.
-- For instance, if the input type has two constructors `C1` and `C2`, the output is:
--
-- match INPUT#1 with
--   C1 x -> f st#3 (C1 x#0) param#1
--   C2 x y -> f st#4 (c2 x#1 y#0) param#2

chooseHeadCase :: (MonadPirouette m)
               => PrtTerm -> PrtType -> [String] -> String -> m PrtTerm
chooseHeadCase t ty args fstArg =
  let argLength = length args in
  let tyOut = snd (R.tyFunArgs ty) in
  case elemIndex fstArg args of
    Nothing -> throwError' $ PEOther "No argument declared as input"
    Just index ->
      let tyInput = fst (R.tyFunArgs ty) !! index in
      case nameOf tyInput of
        Nothing -> throwError' $ PEOther "The input is not of a pattern-matchable type"
        Just tyName -> do
          dest <- blindDest tyOut <$> typeDefOf tyName
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
    nameOf :: PrtType -> Maybe Name
    nameOf (R.TyApp (R.F (TyFree x)) _) = Just x
    nameOf _ = Nothing

    -- `blindDest out ty` constructs the term
    -- match i#1 with
    --   C1 x0 -> f#0 (C1 x0)
    --   C2 x0 x1 -> f#0 (C2 x0 x1)
    -- where `i` is of type `ty` and `f : ty -> out`
    blindDest :: PrtType -> PrtTypeDef -> PrtTerm
    blindDest tyOut (Datatype _ _ dest cons) =
      R.App (R.F (FreeName dest)) $
        R.Arg (R.termPure (R.B (fromString "i") 1)) :
        R.TyArg tyOut :
        map (R.Arg . consCase) cons

    consCase :: (Name, PrtType) -> PrtTerm
    consCase (n, ty) =
      let (argsTy,_) = R.tyFunArgs ty in
      createNLams "x" argsTy $
        R.App
          (R.B (fromString "f") (toInteger (length argsTy)))
          [R.Arg $ R.App (R.F (FreeName n)) (geneXs (length argsTy))]

    -- `createNLams "x" [a,b,c] t` constructs the term
    -- \ (x0 : a) (x1 : b) (x2 : c) -> t
    createNLams :: String -> [PrtType] -> PrtTerm -> PrtTerm
    createNLams s tys =
      let go [] _ = id
          go (h:tl) i =
            R.Lam (R.Ann $ fromString (s ++ show i)) h . go tl (i + 1)
      in
      go tys 0

    -- `geneXs 3` is the representation of `[x0#2, x1#1, x2#0]`,
    -- which are the arguments expected after a `\x0 x1 x2`.
    geneXs :: Int -> [R.Arg ty PrtTerm]
    geneXs n =
      map
        (\i -> R.Arg $ R.termPure (R.B (fromString $ "x" ++ show i) (toInteger $ n - 1 - i)))
        [0 .. n-1]

    -- Replace the argument "INPUT" by a dummy version of it, which is bound at index 0.
    transitionArgs :: String -> Int -> R.Arg ty PrtTerm
    transitionArgs s n
      | s == fstArg = R.Arg $ R.termPure (R.B (fromString "DUMMY_ARG") 0)
      | otherwise   = R.Arg $ R.termPure (R.B (fromString s) (toInteger n))
