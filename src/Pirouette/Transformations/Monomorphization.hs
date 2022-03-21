{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ParallelListComp #-}

module Pirouette.Transformations.Monomorphization(monomorphize) where

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

monomorphize :: forall lang. (LanguagePretty lang, Pretty (FunDef lang), LanguageBuiltins lang)
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
        (defs', specOrders) = runWriter $ transformBiM (specFunApp hofDefs :: SpecFunApp lang) defs
                                      >>= transformBiM (specTyApp  hofDefs :: SpecTyApp  lang)
        newOrders = filter (`S.notMember` prevOrders) specOrders
        newDefs = foldMap executeSpecRequest newOrders

    prune :: PrtUnorderedDefs lang -> PrtUnorderedDefs lang
    prune defs = defs { prtUODecls = M.filterWithKey (\n _ -> n `M.notMember` hofDefs) $ prtUODecls defs }

data SpecRequest lang = SpecRequest
  { origDef :: HofDef lang
  , specArgs :: [Type lang]
  }
  deriving (Show, Eq, Ord)

type SpecFunApp lang = forall m. MonadWriter [SpecRequest lang] m => Term lang -> m (Term lang)
type SpecTyApp  lang = forall m. MonadWriter [SpecRequest lang] m => Type lang -> m (Type lang)

executeSpecRequest :: (LanguageBuiltins lang) => SpecRequest lang -> Decls lang
executeSpecRequest SpecRequest {origDef = HofDef{..}, ..} = M.fromList $
  case hofDefBody of
       HDBFun FunDef{..} -> let newDef = DFunction funIsRec (funBody `SystF.appN` map SystF.TyArg specArgs) (funTy `SystF.appN` specArgs)
                            in [(fixName hofDefName, newDef)]
       HDBType Datatype{..} -> let tyName = fixName hofDefName
                                   dtorName = fixName destructor
                                   ctors = [ (fixName ctorName, foldr (\(n, k) -> SystF.TyLam (SystF.Ann n) k) ctorTy typeVariables `SystF.appN` specArgs)
                                           | (ctorName, ctorTy) <- constructors
                                           ]
                                   newDef = DTypeDef $ Datatype kind [] (fixName destructor) ctors    -- TODO does this only apply to `kind ~ *`?
                                in [ (tyName, newDef)
                                   , (dtorName, DDestructor tyName)
                                   ]
                                <> [ (ctorName, DConstructor i tyName) | (ctorName, _) <- ctors
                                                                       | i <- [0..]
                                   ]
  where
    fixName = genSpecName specArgs

specFunApp :: forall lang. (LanguageBuiltins lang) => HOFDefs lang -> SpecFunApp lang
specFunApp hofDefs (SystF.App (SystF.Free (TermSig name)) args)
  | Just someDef <- name `M.lookup` hofDefs    -- TODO should just the nameString be compared?
  , all isSpecArg $ take hofPolyVarsCount tyArgs = do
    let (specArgs, remainingArgs) = splitArgs hofPolyVarsCount args
        speccedName = genSpecName specArgs name
    tell $ pure $ SpecRequest someDef specArgs
    pure $ SystF.Free (TermSig speccedName) `SystF.App` remainingArgs
  where
    tyArgs = mapMaybe SystF.fromTyArg args
    hofPolyVarsCount = 1 -- TODO don't hardcode 1
specFunApp _ x = pure x

specTyApp :: (LanguageBuiltins lang) => HOFDefs lang -> SpecTyApp lang
specTyApp hofDefs (SystF.TyApp (SystF.Free (TySig name)) tyArgs)
  | Just someDef <- name `M.lookup` hofDefs
  , all isSpecArg $ take hofPolyVarsCount tyArgs = do
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

findPolyFuns :: LanguageBuiltins lang
             => (FunDef lang -> Bool)
             -> [(Name, Definition lang)]
             -> [(Name, HofDef lang)]
findPolyFuns predi = flip findFuns (\f -> isPolyType (funTy f) && predi f)

isPolyType :: SystF.AnnType ann ty -> Bool
isPolyType SystF.TyAll {} = True
isPolyType _ = False


hofsClosure :: forall lang. (LanguageBuiltins lang, LanguagePretty lang) => Decls lang -> HOFDefs lang -> HOFDefs lang
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
        hasHofName entity = not (null [ () | TySig name   <- universeBi entity :: [TypeBase lang], name `M.member` hofs ])
                         || not (null [ () | TermSig name <- universeBi entity :: [TermBase lang], name `M.member` hofs ])
