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
cfoldmapSpecialize = pushCtx "cfoldmapSpecialize" . rewriteM (runMaybeT . go)
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
      (n, tyN, tyArgs, x, tyReturn@(R.TyFun tyA tyB), cases) <- unDest t
      Datatype _ _ _ cons <- lift $ typeDefOf tyN
      let nbCons = length cons
      let (cases', excess) = splitAt nbCons cases
      if null excess
      then fail "Destruction to a function type without excessive arguments"
      else do
        logTrace $ show n
        return $
          R.App (R.F $ FreeName n) $
            map R.TyArg tyArgs
              ++ [R.Arg x, R.TyArg $ tyDrop (length excess) tyReturn]
              ++ zipWith (\(_,cty) t -> R.Arg $ appExcessive excess cty t) cons cases'

    appExcessive :: [PrtTerm] -> Type Name -> PrtTerm -> PrtTerm
    appExcessive l (R.TyFun a b) (R.Lam n ty t) =
      R.Lam n ty (appExcessive (map (shift 1) l) b t) -- `a` and `ty` are equal, up to substitution of variables in the type of the constructors.
    appExcessive l (R.TyFun a b) _              =
       undefined -- When matching, the number of lambdas should be bigger than the number of arguments of a constructor.
    appExcessive l _             t              =
       R.appN t $ map R.Arg l

    tyDrop :: Int -> PrtType -> PrtType
    tyDrop 0 t             = t
    tyDrop n (R.TyFun a b) = tyDrop (n-1) b
    tyDrop n t             = undefined -- If `n` is not 0, then the type must be an arrow.

-- |Simpler version of 'removeExcessiveArgs' that removes arguments of type Unit only.
removeThunks :: (MonadPirouette m) => PrtTerm -> m PrtTerm
removeThunks = pushCtx "removeThunks" . rewriteM (runMaybeT . go)
  where
    go :: (MonadPirouette m) => PrtTerm -> MaybeT m PrtTerm
    go t = do
      (n, tyN, tyArgs, x, R.TyFun tyA tyB, cases) <- unDest t
      isUnit <- lift $ typeIsUnit tyA
      if not isUnit then fail "Can't rewrite; not Unit"
      else do
        let (cases', [unit]) = splitAt (length cases - 1) cases
        logTrace $ show n
        return $ R.App (R.F $ FreeName n)
               $ map R.TyArg tyArgs
              ++ [R.Arg x, R.TyArg tyB]
              ++ map (R.Arg . (`appLast` unit)) cases'

    appLast :: (HasSubst ty, IsVar f)
            => R.AnnTerm ty ann f -> R.AnnTerm ty ann f -> R.AnnTerm ty ann f
    appLast t@(R.Lam _ _ (R.App _ _)) arg = R.termApp t (R.Arg arg)
    appLast (R.Lam ann ty t)          arg = R.Lam ann ty (appLast t arg)
    appLast t                         arg = R.termApp t (R.Arg arg)

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
      (_, tyN, tyArgs, x, ret, cases) <- unDest t
      (tyN', xTyArgs, xIdx, xArgs) <- unCons x
      guard (tyN == tyN')
      ar <- length . constructors <$> lift (typeDefOf tyN)
      let (cases0, rest) = splitAt ar cases
      let xCase          = cases0 !! xIdx
      logTrace $ show tyN
      return $ R.appN (R.appN xCase (map R.Arg xArgs)) (map R.Arg rest)

-- |Returns the equiavlent /destructor normal-form/ (DNF) term.
-- We say a term is in /destructor normal-form/ when all destructors
-- are pushed to the root of the term. For example, take
--
-- > t = [f [d/Maybe x N (\ J)] a0 a1]
--
-- If @f@ is also a destructor and @N@ and @J@ are in DNF, then @t@ is in DNF,
-- otherwise, we return:
--
-- >  [d/Maybe x $(destrNF [f N a0 a1]) (\ $(destrNF [f J a0 a1]))]
--
-- that is, we push the application of f down to the branches of the "case" statement.
destrNF :: forall m . (MonadPirouette m) => PrtTerm -> m PrtTerm
destrNF = pushCtx "destrNF" . rewriteM (runMaybeT . go)
  where
    onApp :: (R.Var Name (PIRBase P.DefaultFun Name)
               -> [R.Arg PrtType PrtTerm] -> MaybeT m PrtTerm)
          -> PrtTerm -> m PrtTerm
    onApp f t@(R.App n args) = fromMaybe t <$> runMaybeT (f n args)
    onApp _ t                = return t

    -- Returns a term that is a destructor from a list of terms respecting
    -- the invariant that if @splitDest t == Just (xs , d , ys)@, then @t == xs ++ [d] ++ ys@
    splitDest :: [R.Arg PrtType PrtTerm]
              -> MaybeT m ( PrtTerm
                          , ListZipper (R.Arg PrtType PrtTerm))
    splitDest [] = fail "splitDest: can't split empty list"
    splitDest (a@(R.Arg a2@(R.App (R.F (FreeName n)) args)) : ds) =
          (isDest n >> return (a2, ListZipper ([], ds)))
      <|> (splitDest ds <&> second (zipperCons a))
    splitDest (a : ds) = splitDest ds <&> second (zipperCons a)

    go :: PrtTerm -> MaybeT m PrtTerm
    go (R.App (R.B _ _)           fargs) = fail "destrNF.go: bound name"
    go (R.App (R.F (FreeName fn)) fargs) = do
      -- check this is an application that is /not/ a destructor then
      -- try to see if there's at least one destructor in the arguments.
      -- If we find a destructor within the arguments, we can make sure it
      -- is an `App` and has at least one argument, the value being eliminated.
      notM (isDest fn)
      (dest, fargsZ) <- splitDest fargs
      (dn, tyN, tyArgs, x, ret, cases) <- unDest dest
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

-- |Assuming a DNF term, swap the nth and the (n+1)th destructor counting from the root being 0.
swapNthDestr :: (MonadPirouette m) => Int -> PrtTerm -> MaybeT m PrtTerm
swapNthDestr 0 t                  = swapDestr t
swapNthDestr n (R.Abs v ki t)     = R.Abs v ki <$> swapNthDestr n t
swapNthDestr n (R.Lam v ty t)     = R.Lam v ty <$> swapNthDestr n t
swapNthDestr n t = do
  (dname, tyN, tyArgs, x, ret, cases) <- unDest t
  cases' <- mapM (swapNthDestr (n-1)) cases
  return $ R.App (R.F $ FreeName dname)
               $ map R.TyArg tyArgs ++ [R.Arg x, R.TyArg ret] ++ map R.Arg cases'

-- |Assuming a DNF term, pulls the n-th destructor to the top-level by swapping it
-- with the (n-1)-th, then (n-2)-th, etc. until we swap with the topmost destructor.
pullNthDestr :: (MonadPirouette m) => Int -> PrtTerm -> m PrtTerm
pullNthDestr n t = do
  mres <- runMaybeT $ foldl' (\m i -> m >>= swapNthDestr i) (return t) [n-1,n-2 .. 0]
  case mres of
    Nothing -> throwError' $ PEOther $ "Can't pull destructor indexed " ++ show n
    Just r  -> return r


-- |Swaps two destructors at the top level, if possible. It is possible to swap
-- destructors for types /T0/ and /T1/ whenever all branches following the matching
-- of /x :: T0/ immediately match on /y :: T1/, such that /y/ doesn't depend on any value
-- that comes from a constructor of @x@. Take the following term @t@ as an example:
--
-- > [dMaybe x         [dEither yN (\ly -> LN) (\ry -> RN)]
-- >           (\jx -> [dEither yJ (\ly -> LJ) (\ry -> RJ)])]
--
-- Both the /Nothing/ and the /Just/ branch immediately match on an @Either@;
-- Now assume @yJ@ does not depend on #0, which comes from matching the @Just@ constructor
-- and @yJ == shift 1 0 yN@, then we can swap matching on @x@ with matching on @y@:
--
-- > [dEither y (\ly -> [dMaybe xL LN' (\jx -> LJ')])
-- >            (\ry -> [dMaybe xR RN' (\jx -> RJ')])
--
-- Lets start defining the easy bits first:
--
--  - @y@ is defined as @yN@ or @shift -1 yJ@
--  - @xL@ is defined by shifting @x@ by the amount of lambdas in the @Left@ constructor,
--    in this case @shift 1 0 x@,
--  - @xR@ is analogous to @xL@
--  - @LN'@ is equal to @shift 0 0 LN@, which is just @LN@ (because Nothing receives zero arguments)
--  - @RN'@ is equal to @RN@, analogously to @LN'@
--
-- Now we have to define @LJ'@ and @RJ'@, which is a little more complex since we have to permute
-- variables. In this case, we permute #0 with #1 and thats it, in general its a little
-- more hairy. Say we're dealing with the following swap:
--
-- > x = [dT ... (\\ [dU ... (\\\ M)])] ~> [dU ... (\\\ [dT ... (\\ M')])] = x'
--
-- The term @M'@ is the same as @M@, but with the following permutation, @f@ applied
-- to the free variables of @M@:
--
-- > f 0 = 2
-- > f 1 = 3
-- > f 2 = 4    => f x = (x + 2) `mod` 5, where 2 is li in the /adapt/ function below
-- > f 3 = 0
-- > f 4 = 1
--
-- When applying said permutation, however, we must also do so in a scoped manner.
-- Say we traversed two lambdas within @M@, and found variable #6 somewhere inside. That
-- is the same as variable #4 outside those two lambdas, or, in other words, the first
-- argument of the constructor of type @T@. To map that to the same variable in @x'@ we
-- have map that to @2 + f (6 - 2)@, which is #3, and will refer to the correct variable.
-- That adjustment is the responsibility of the 'permute' function, however.
--
swapDestr :: (MonadPirouette m) => PrtTerm -> MaybeT m PrtTerm
swapDestr (R.Abs x ty body)     = R.Abs x ty <$> swapDestr body
swapDestr (R.Lam x ty body)     = R.Lam x ty <$> swapDestr body
swapDestr t = pushCtx "swapDestr" $ do
  -- First we check n is a destructor, then we check that all branches of the matches are also
  -- destructors of the same type and the same value.
  (dName, tyName, tyArgs, x, ret, args) <- unDest t
  args' <- mapM toScopedDestApp args
  guard (allEqualBy sameDestVal args')
  -- we must have at least one branch to look at, otherwise we're destructing an element
  -- of the void type.
  let b:bs = args'
  logTrace $ "Swapping " ++ show dName ++ " with " ++ show (destName b)
  -- given all the checks above passed, we're ready to construct the resulting term.
  -- Following the example with Maybe and Either in the comment above, we have
  --
  -- > destOf b == d/Either
  -- > destVal b == yN
  -- > map (split cutoff branches) args' == ([],     [ (["ly"], LN), (["ry"], RN) ])
  -- >                                    : (["jx"], [ (["ly"], LJ), (["ry"], RH) ])
  -- >                                    : []
  --
  -- Now, we want to distribute the cutoff coming from the d/Maybe,
  -- then transpose that "matrix" of terms, swap the cutoffs, then undistribute cutoff
  -- from d/Either, yielding the ms below.
  --
  -- > ms == [ (["ly"], [([], LN), (["jx"], LJ)])
  -- >       , (["ry"], [([], RN), (["jx"], RJ)])
  -- >       ]
  --
  -- The 'processMatrix' function will do that for us.
  let ms = processMatrix $ map (\sda -> map (cutoff' sda,) (branches sda)) args'

  -- It could happen that the two "ly" (arguments of the constructor)
  -- are not the same in every branch. Since we keep the ones of the first branch,
  -- we have to do some renamings in the other branches.
  let ms' = map rename ms
  -- Finally, we build the functon that will reconstruct the cases of the outer
  -- destructor. When swapping the two Maybe and Either above, 'go' will be called twice:
  --
  -- > go dMaybe x 1 [(0, LN) , (1, LJ)]
  -- > go dMaybe x 1 [(0, RN) , (1, RJ)]
  --
  -- The second call, for example, should return:
  --
  -- > \ [dMaybe $(shift 1 x) $(adapt 1 0 RN) $(adapt 1 1 RJ)]
  --
  let go c bs = R.withLams c $ R.App (R.F $ FreeName dName)
                                 $ map R.TyArg tyArgs
                               ++ [R.Arg (shift (toInteger $ length c) x), R.TyArg ret]
                               ++ map (R.Arg . uncurry (adapt c)) bs

  return $ R.App (R.F $ FreeName $ destName b)
               $ map R.TyArg (snd $ destOf b)
              ++ [R.Arg (shift (-(cutoff b)) (destVal b)), R.TyArg (destRetTy b)]
              ++ map (R.Arg . uncurry go) ms'
  where
    allEqualBy :: (a -> a -> Bool) -> [a] -> Bool
    allEqualBy rel = (== 1) . length . groupBy rel

    processMatrix :: [[(n, (i, a))]] -> [(i, [(n, a)])]
    processMatrix = map (first head . unzip) . transpose . map (map (\(i, (n, a)) -> (n, (i, a))))

    rename :: ([(Name,a)],[(n,PrtTerm)]) -> ([(Name,a)],[(n,PrtTerm)])
    rename (x,l) =
      (x, map (second (R.renameFirstBounds (reverse (map fst x)))) l)

    adapt :: [(Name, PrtType)] -> [(Name, PrtType)]
          -> PrtTerm -> PrtTerm
    adapt outer [] t = t
    adapt outer i  t =
      let louter = toInteger $ length outer
          li     = toInteger $ length i
       in R.withLams i (R.permute (\x -> if x >= li + louter then x else (x + li) `mod` (louter + li)) t)

-- * Auxiliar Definitions

-- |A 'ScopedDestApp' represents a "a match within a match". When we have:
--
-- > case x :: Maybe Int of
-- >   Just i -> [t0| case y :: Either Bool Bool of
-- >                    Left l -> M; Right r -> N
-- >             |]
-- >   ...
--
-- The marked splice @t0@ could be writen as a 'ScopedDestApp' with:
--
-- > t0 = ScopedDestApp { cutoff' = ["i"]
-- >                    , destOf  = "Either"
-- >                    , destVal = "y"
-- >                    , branches = [(["l"], M), (["r"], N)] }
--
-- We keep the bound names in here to attempt to preserve the user-provided
-- names as much as possible.
data ScopedDestApp = ScopedDestApp
  { destName   :: Name
  , cutoff'    :: [(Name, PrtType)]
  , destOf     :: (Name, [PrtType])
  , destVal    :: PrtTerm
  , destRetTy  :: PrtType
  , branches   :: [([(Name, PrtType)], PrtTerm)]
  } deriving (Show)

cutoff :: ScopedDestApp -> Integer
cutoff = toInteger . length . cutoff'

-- |Two terms being destructed in a /ScopedDestApp/ are the same when they are being
-- destructed by the same type and except for the cutoff variables, they are equal.
sameDestVal :: ScopedDestApp -> ScopedDestApp -> Bool
sameDestVal sda1 sda2 = destOf sda1 == destOf sda2
                     && destRetTy sda1 == destRetTy sda2 -- TODO: do we need this?
                     && shift (-(cutoff sda1)) (destVal sda1) == shift (-(cutoff sda2)) (destVal sda2)

-- |Checks whether a term is a sequence of lambdas followed by a destructor application,
-- if so, keep all the relevant information in a record to help us stay organized.
toScopedDestApp :: (MonadPirouette m) => PrtTerm -> MaybeT m ScopedDestApp
toScopedDestApp = go []
  where
    go c (R.Abs _         ty body) = fail "toScopedDestApp: type abstraction inside destructor"
    go c (R.Lam (R.Ann n) ty body) = go ((n, ty):c) body
    go c t = do
      (nName, tyName, tyArgs, x, ret, args) <- unDest t
      return $ ScopedDestApp nName (reverse c) (tyName, tyArgs) x ret (map R.getHeadLams args)

-- |A 'ListZipper' is a zipper as in one-hole-contexts
newtype ListZipper a = ListZipper { unListZipper :: ([a], [a]) }

instance Functor ListZipper where
  fmap f (ListZipper (xs, xs')) = ListZipper (map f xs, map f xs')

plug :: a -> ListZipper a -> [a]
plug a (ListZipper (xs, xs')) = xs ++ [a] ++ xs'

zipperCons :: a -> ListZipper a -> ListZipper a
zipperCons a (ListZipper (xs, xs')) = ListZipper (a:xs, xs')
