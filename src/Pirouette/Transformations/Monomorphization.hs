{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Transformations.Monomorphization (monomorphize, hofsClosure, findPolyHOFDefs, specFunApp, SpecRequest (..)) where

import Control.Monad.Writer.Strict
import Data.Data
import Data.Generics.Uniplate.Data
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils

-- * Monomorphization

--
-- tl;dr: `monomorphize` exported from this module turns (in Haskell syntax)
--
-- > foldl :: (b -> a -> b) -> b -> [a] -> b
-- > foldl f z []     = z
-- > foldl f z (x:xs) = foldl f (f z x) xs
-- >
-- > any :: [Bool] -> Bool
-- > any xs = foldl or False xs
--
-- into, imagining '@' is a valid part of a name:
--
-- > foldl@Bool@Bool :: (Bool -> Bool -> Bool) -> Bool -> [Bool] -> Bool
-- > foldl@Bool@Bool f z []     = z
-- > foldl@Bool@Bool f z (x:xs) = foldl@Bool@Bool f (f z x) xs
-- >
-- > any :: [Bool] -> Bool
-- > any xs = foldl@Bool@Bool or False xs
--
-- This module implements a _partial_ monomorphization,
-- substituting type variables appearing in higher-order functional contexts with the specific types.
-- That is,
--
-- > foo :: (a -> a -> a) -> b -> b
-- > bar :: _
-- > bar = foo (\(l :: Bool) (r :: Bool) -> l `or` r) "test"
--
-- results in
--
-- > foo@Bool :: (Bool -> Bool -> Bool) -> b -> b
-- > bar :: _
-- > bar = foo@Bool ...
--
-- and _not_ in `foo@Bool@String`: we don't specialize `b` since it doesn't appear in a higher-order context.
--
-- Polymorphic data types like `Maybe` or
--
-- > data Monoid a where
-- >   MkMonoid :: (a -> a -> a) -> a -> Monoid a
--
-- are handled similarly.
--
--
-- -- * Motivation
--
-- This is just about as much as needed to prepare a System Fω program for symbolic evaluation with an SMT solver.
-- Indeed, current SMTLIB doesn't support higher-order functions, hence we need to defunctionalize.
--
-- It seemingly isn't possible to defunctionalize polymoprhic higher-order functions in System Fω
-- (as the imaginary polymorphic `apply` function is not typeable),
-- so we need to monomorphize everything higher-order before defunctionalization.
-- And, since SMTLIB does support polymorphism, we can leave type variables not occuring in a higher-order context,
-- potentially reducing the number of extra specialized terms.
--
-- -- * Shortcomings
--
-- The tl;dr example is actually a bit of wishful thinking: right now, only the first type variable gets monomorphized.
-- The example is what the module will eventually do, but full monomorphization on all tyvars is TODO for now.

-- | The ultimate monomorphization, orchestrating the rest of the functions in this module.
--
-- Monomorphization goes as follows:
--
-- 1. The higher-order polymorphic definitions are collected (via 'findPolyHOFDefs'):
--    * all the functions having functional arguments of polymorphic type,
--    * all the types having at least one constructor having a polymorphic HOF field.
-- 2. The transitive closure of functions mentioning the names of things from step (1) is built (via 'hofDefs').
-- 3. a. All mentions of names from (2) applied to concrete types only (where no type variables are present)
--       are replaced with a specialized name, so @foldl @Bool @Bool f x y@ becomes @foldl_Bool_Bool f x y@
--       (via 'specFunApp' and 'specTyApp').
--    b. The definitions corresponding to the names found during step (a) get generated:
--       so, if step (a) replaced @fold @Bool @Bool@ with @fold_Bool_Bool@ somewhere, then this step
--       actually generates the definition of @fold_Bool_Bool@ based on the "template" @fold@.
-- 4. Since step (3b) might introduce more names from (2) applied to concrete types,
--    the whole step (3) is repeated until the fixpoint
--    (which presumably might not exist for arbitrary System Fω, but shall exist for the subset of programs we care about).
-- 5. Having done that, all the higher-order definitions from (2) are subject to @prune@.
--    If step (3) works correctly, then they are not used transitively from the modified main term.
monomorphize :: forall lang. (Language lang)
             => PrtUnorderedDefs lang
             -> PrtUnorderedDefs lang
monomorphize defs0 = prune $ go mempty defs0
  where
    hofDefsRoots = findPolyHOFDefs $ prtUODecls defs0
    hofDefs = hofsClosure (prtUODecls defs0) hofDefsRoots

    go :: S.Set (SpecRequest lang) -> PrtUnorderedDefs lang -> PrtUnorderedDefs lang
    go prevOrders defs
      | M.null newDefs && defs == defs' = defs'
      | otherwise = go (prevOrders <> S.fromList newOrders) $ addDecls newDefs defs'
      where
        (defs', specOrders) =
          runWriter $
            transformBiM (specFunApp hofDefs :: SpecFunApp lang) defs
              >>= transformBiM (specTyApp hofDefs :: SpecTyApp lang)
        newOrders = filter (`S.notMember` prevOrders) specOrders
        newDefs = foldMap executeSpecRequest newOrders

    prune :: PrtUnorderedDefs lang -> PrtUnorderedDefs lang
    prune defs = defs {prtUODecls = M.filterWithKey (\n _ -> n `M.notMember` hofDefs) $ prtUODecls defs}

-- | Describes a definition (a function or a type) that needs to be specialized with the given type arguments list.
data SpecRequest lang = SpecRequest
  { origDef :: HofDef lang,
    specArgs :: [Type lang]
  }
  deriving (Show, Eq, Ord)

type SpecFunApp lang = forall m. MonadWriter [SpecRequest lang] m => Term lang -> m (Term lang)

type SpecTyApp lang = forall m. MonadWriter [SpecRequest lang] m => Type lang -> m (Type lang)

-- | Takes a description of what needs to be specialized
-- (a function or a type definition along with specialization args)
-- and produces the specialized definitions.
executeSpecRequest :: (Language lang) => SpecRequest lang -> Decls lang
executeSpecRequest SpecRequest {origDef = HofDef {..}, ..} = M.fromList $
  case hofDefBody of
    HDBFun FunDef {..} ->
      let newDef =
            DFunction
              funIsRec
              (funBody `SystF.appN` map SystF.TyArg specArgs)
              (funTy `SystF.tyInstantiateN` specArgs)
       in [(fixName hofDefName, newDef)]
    HDBType Datatype {..} ->
      let tyName = fixName hofDefName
          dtorName = fixName destructor
          ctors =
            [ (fixName ctorName, ctorTy `SystF.tyInstantiateN` specArgs)
              | (ctorName, ctorTy) <- constructors
            ]
          newDef = DTypeDef $ Datatype kind [] (fixName destructor) ctors -- TODO does this only apply to `kind ~ *`?
       in [ (tyName, newDef),
            (dtorName, DDestructor tyName)
          ]
            <> [ (ctorName, DConstructor i tyName)
                 | (ctorName, _) <- ctors
                 | i <- [0 ..]
               ]
  where
    fixName = genSpecName specArgs

-- | Specializes a function application of the form:
--
--  > hof @Integer x y z
--
-- at call site, where @hof@ has been identified as
-- 1. either a higher-order function itself,
-- 2. or invoking a polymorphic higher-order function, perhaps, transitively;
-- and its type argument contains no bound-variables: in other words,
-- we can substitute that call with @hof_Integer@ while creating a monomorphic
-- definition for @hof@.
--
-- This function only does the substitution _at call site_ and emits a 'SpecRequest' denoting that the corresponding
-- higher-order _definition_ needs to be specialized (which will be handled later by 'executeSpecRequest').
specFunApp :: forall lang. (LanguageBuiltins lang) => HOFDefs lang -> SpecFunApp lang
specFunApp hofDefs (SystF.App (SystF.Free (TermSig name)) args)
  | Just someDef <- name `M.lookup` hofDefs, -- We compare the entire name, not just the nameString part: x0 /= x1.
    all isSpecArg $ take hofPolyVarsCount tyArgs = do
    let (specArgs, remainingArgs) = splitArgs hofPolyVarsCount args
        speccedName = genSpecName specArgs name
    tell $ pure $ SpecRequest someDef specArgs
    pure $ SystF.Free (TermSig speccedName) `SystF.App` remainingArgs
  where
    tyArgs = mapMaybe SystF.fromTyArg args
    hofPolyVarsCount = 1 -- TODO don't hardcode 1
specFunApp _ x = pure x

-- |Specializes a type application of the form
--
-- > HOFType @Integer
--
-- where @HOFType a@ has at least one constructor having a higher-order argument mentioning @a@,
-- perhaps, transitively.
-- For example, both these definitions would be specialized:
--
-- > data Semigroup a = MkSemigroup (a -> a -> a)
-- > data Monoid a = MkMonoid (Semigroup a) a
--
-- See the docs for 'specFunApp' for more details.
specTyApp :: (LanguageBuiltins lang) => HOFDefs lang -> SpecTyApp lang
specTyApp hofDefs (SystF.TyApp (SystF.Free (TySig name)) tyArgs)
  | Just someDef <- name `M.lookup` hofDefs,
    all isSpecArg $ take hofPolyVarsCount tyArgs = do
    let (specArgs, remainingArgs) = splitAt hofPolyVarsCount tyArgs
        speccedName = genSpecName specArgs name
    tell $ pure $ SpecRequest someDef specArgs
    pure $ SystF.Free (TySig speccedName) `SystF.TyApp` remainingArgs
  where
    hofPolyVarsCount = 1 -- TODO don't hardcode 1
specTyApp _ x = pure x

-- TODO the above definition shouldn't have hofPolyVarsCount as the _count_,
-- since the HOF-involved type args aren't necessarily at the front of the application.
-- A smarter approach would be to keep a list of type variables need to be monomorphized,
-- but this kludge together with hardcoding it to be `1` gets us far enough
-- to work with SMT on some realistic examples.

genSpecName :: (LanguageBuiltins lang) => [Type lang] -> Name -> Name
genSpecName args name = Name (nameString name <> "@" <> argsToStr args) Nothing

-- A type argument is fully specialized if it has no bound variables
isSpecArg :: forall lang. LanguageBuiltins lang => Type lang -> Bool
isSpecArg arg = null bounds
  where
    bounds :: [TyVar lang]
    bounds = filter (isJust . isBound) $ universeBi arg

-- Returns the definitions containing (polymorphic) higher-order functions,
-- be it functions or types.
--
-- The returned Map maps any name that contains higher-order stuff.
-- In particular, for a type it contains the type itself as well as
-- the type's constructors and destructor.
findPolyHOFDefs :: LanguageBuiltins lang => Decls lang -> HOFDefs lang
findPolyHOFDefs = findHOFDefs (isPolyType . funTy) (const $ const True) . M.toList

findPolyFuns ::
  LanguageBuiltins lang =>
  (FunDef lang -> Bool) ->
  [(Name, Definition lang)] ->
  [(Name, HofDef lang)]
findPolyFuns predi = flip findFuns (\f -> isPolyType (funTy f) && predi f)

isPolyType :: SystF.AnnType ann ty -> Bool
isPolyType SystF.TyAll {} = True
isPolyType _ = False

-- | Finds the transitive closure of functions invoking higher-order things.
--
-- > hofsClosure decls hofDefs
--
-- returns the set of type or function definitions (a subset of @decls@)
-- that transitively mention names in @hofDefs@.
hofsClosure :: forall lang. (Language lang) => Decls lang -> HOFDefs lang -> HOFDefs lang
hofsClosure decls = go
  where
    declsPairs = M.toList decls

    go hofs
      | hofs == hofs' = hofs
      | otherwise = go hofs'
      where
        hofs' = hofs <> M.fromList (hofTypes' <> hofFuns')
        hofTypes' = findTypes declsPairs $ \_ typeDef -> hasHofName typeDef
        hofFuns' = findPolyFuns hasHofName declsPairs

        hasHofName :: (Data a) => a -> Bool
        hasHofName entity =
          not (null [() | TySig name <- universeBi entity :: [TypeBase lang], name `M.member` hofs])
            || not (null [() | TermSig name <- universeBi entity :: [TermBase lang], name `M.member` hofs])
