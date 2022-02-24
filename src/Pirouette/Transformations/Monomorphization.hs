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
import Data.Bifunctor
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Text as Text
import Prettyprinter hiding (Pretty, pretty)

import Debug.Trace

import Pirouette.Monad
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst
import Pirouette.Term.Syntax.SystemF hiding (Var)

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

traceDefsId :: (PrettyLang builtins) => PrtUnorderedDefs builtins -> PrtUnorderedDefs builtins
traceDefsId defs = renderSingleLineStr (pretty $ prtUODecls defs) `trace` defs

monomorphize :: forall builtins. (PrettyLang builtins, Pretty (FunDef builtins), LanguageBuiltins builtins)
             => PrtUnorderedDefs builtins
             -> PrtUnorderedDefs builtins
monomorphize defs0 = traceDefsId (prune $ go mempty defs0)
  where
    hofDefsRoots = findHOFDefs $ prtUODecls defs0
    hofDefs = hofsClosure (prtUODecls defs0) hofDefsRoots

    go :: Set.Set (SpecRequest builtins) -> PrtUnorderedDefs builtins -> PrtUnorderedDefs builtins
    go prevOrders defs
      | Map.null newDefs && defs == defs' = defs'
      | otherwise = -- renderSingleLineStr (pretty (head $ Map.elems $ head $ executeSpecRequest <$> specOrders)) `trace`
                    go (prevOrders <> Set.fromList newOrders) $ addDecls newDefs defs'
      where
        (defs', specOrders) = runWriter $ transformBiM (specFunApp hofDefs :: SpecFunApp builtins) defs
                                      >>= transformBiM (specTyApp  hofDefs :: SpecTyApp  builtins)
        newOrders = filter (`Set.notMember` prevOrders) specOrders
        newDefs = foldMap executeSpecRequest newOrders

    prune :: PrtUnorderedDefs builtins -> PrtUnorderedDefs builtins
    prune defs = defs { prtUODecls = Map.filterWithKey (\n _ -> n `Map.notMember` hofDefs) $ prtUODecls defs }

data SpecRequest builtins = SpecRequest
  { origDef :: HofDef builtins
  , specArgs :: [Type builtins]
  }
  deriving (Show, Eq, Ord)

type SpecFunApp builtins = forall m. MonadWriter [SpecRequest builtins] m => Term builtins -> m (Term builtins)
type SpecTyApp  builtins = forall m. MonadWriter [SpecRequest builtins] m => Type builtins -> m (Type builtins)

executeSpecRequest :: (LanguageBuiltins builtins) => SpecRequest builtins -> Decls builtins
executeSpecRequest SpecRequest {origDef = HofDef{..}, ..} = Map.fromList $
  case hofDefBody of
       HDBFun FunDef{..} -> let newDef = DFunction funIsRec (funBody `appN` map TyArg specArgs) (funTy `appN` specArgs)
                            in [(fixName hofDefName, newDef)]
       HDBType Datatype{..} -> let tyName = fixName hofDefName
                                   dtorName = fixName destructor
                                   ctors = [ (fixName ctorName, foldr (\(n, k) -> TyLam (Ann n) k) ctorTy typeVariables `appN` specArgs)
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

specFunApp :: forall builtins. (LanguageBuiltins builtins) => HOFDefs builtins -> SpecFunApp builtins
specFunApp hofDefs (App (Free (TermFromSignature name)) args)
  | Just someDef <- name `Map.lookup` hofDefs    -- TODO should just the nameString be compared?
  , all isSpecArg $ take (hofPolyVarsCount someDef) tyArgs = do
    let (specArgs, remainingArgs) = splitArgs (hofPolyVarsCount someDef) args
        speccedName = genSpecName specArgs name
    tell $ pure $ SpecRequest someDef specArgs
    pure $ Free (TermFromSignature speccedName) `App` remainingArgs
  where
    tyArgs = mapMaybe fromTyArg args
    splitArgs 0 args = ([], args)
    splitArgs n (TyArg tyArg : args) = first (tyArg :) $ splitArgs (n - 1) args
    splitArgs n (arg : args) = second (arg :) $ splitArgs n args
    splitArgs _ [] = error "Less args than poly args count"
specFunApp _ x = pure x

specTyApp :: (LanguageBuiltins builtins) => HOFDefs builtins -> SpecTyApp builtins
specTyApp hofDefs (TyApp (Free (TypeFromSignature name)) tyArgs)
  | Just someDef <- name `Map.lookup` hofDefs
  , all isSpecArg $ take (hofPolyVarsCount someDef) tyArgs = do
    let (specArgs, remainingArgs) = splitAt (hofPolyVarsCount someDef) tyArgs
        speccedName = genSpecName specArgs name
    tell $ pure $ SpecRequest someDef specArgs
    pure $ Free (TypeFromSignature speccedName) `TyApp` remainingArgs
specTyApp _ x = pure x

argsToStr :: (LanguageBuiltins builtins) => [Type builtins] -> Text.Text
argsToStr = Text.intercalate "@" . map f
  where
    f (Free (TypeFromSignature n) `TyApp` []) = nameString n
    f (Free (TypeFromSignature n) `TyApp` args) = nameString n <> "<" <> argsToStr args <> ">"
    f arg = error $ "unexpected specializing arg" <> show arg

genSpecName :: (LanguageBuiltins builtins) => [Type builtins] -> Name -> Name
genSpecName args name = Name (nameString name <> "@" <> argsToStr args) Nothing

-- A type argument is fully specialized if it has no bound variables
isSpecArg :: forall builtins. LanguageBuiltins builtins => Type builtins -> Bool
isSpecArg arg = null bounds
  where
    bounds :: [Var builtins]
    bounds = filter (isJust . isBound) $ universeBi arg

-- Types can't depend on terms, so it's safe to move all type applications to the front.
-- Also, this function is obviously broken right now.
reorderAppTys :: forall builtins. LanguageBuiltins builtins
              => PrtUnorderedDefs builtins
              -> PrtUnorderedDefs builtins
reorderAppTys = transformBi f . error "this is currently broken"
  where
    f :: Term builtins -> Term builtins
    f (App vm args) = App vm (reorder args)
    f t = t

    -- TODO fix de Bruijn indices
    reorder = uncurry (<>) . partition isTyArg

data HofDefBody builtins
  = HDBType (TypeDef builtins)
  | HDBFun  (FunDef builtins)
  deriving (Show, Eq, Ord)

data HofDef builtins = HofDef
  { hofDefName :: Name
  , hofPolyVarsCount :: Int
  , hofDefBody :: HofDefBody builtins
  }
  deriving (Show, Eq, Ord)
-- TODO the above definition shouldn't have hofPolyVarsCount as the _count_,
-- since the HOF-involved type args aren't necessarily at the front of the application.
-- A smarter approach would be to keep a list of type variables need to be monomorphized,
-- but this kludge together with hardcoding it to be `1` gets us far enough
-- to work with SMT on some realistic examples.

type HOFDefs builtins = Map.Map Name (HofDef builtins)

-- Returns the definitions containing higher-order functions,
-- be it functions or types.
--
-- The returned Map maps any name that contains higher-order stuff.
-- In particular, for a type it contains the type itself as well as
-- the type's constructors and destructor.
findHOFDefs :: LanguageBuiltins builtins => Decls builtins -> HOFDefs builtins
findHOFDefs decls = Map.fromList $ hofTypes <> hofFuns
  where
    hofTypes = mkTypeHofDefs declsPairs $ \_ typeDef -> (hasHOFuns . snd) `any` constructors typeDef
    hofFuns = [ (name, HofDef name 1 $ HDBFun funDef)  -- TODO don't hardcode 1
              | (name, DFunDef funDef) <- declsPairs
              , hasHOFuns $ funTy funDef
              ]
    declsPairs = Map.toList decls

mkTypeHofDefs :: LanguageBuiltins builtins
              => [(Name, Definition builtins)]
              -> (Name -> TypeDef builtins -> Bool)
              -> [(Name, HofDef builtins)]
mkTypeHofDefs declsPairs pred =
  [ (name, HofDef tyName 1 $ HDBType typeDef)  -- TODO don't hardcode 1
  | (tyName, DTypeDef typeDef) <- declsPairs
  , pred tyName typeDef
  , name <- tyName : destructor typeDef : (fst <$> constructors typeDef)
  ]

hasHOFuns :: (Data ann, Data ty) => AnnType ann ty -> Bool
hasHOFuns ty = isHOFTy `any` [ f | f@TyFun {} <- universe ty ]

isHOFTy :: AnnType ann ty -> Bool
isHOFTy (TyFun TyFun {} _) = True
isHOFTy _ = False


hofsClosure :: forall builtins. (LanguageBuiltins builtins, PrettyLang builtins) => Decls builtins -> HOFDefs builtins -> HOFDefs builtins
hofsClosure decls = go
  where
    declsPairs = Map.toList decls

    go hofs
      | hofs == hofs' = hofs
      | otherwise = hofs'
      where
        hofs' = hofs <> Map.fromList (hofTypes' <> hofFuns')
        hofTypes' = mkTypeHofDefs declsPairs $ \tyName typeDef -> tyName `Map.notMember` hofs
                                                               && hasHofName typeDef
        hofFuns' = [ (name, HofDef name 1 $ HDBFun funDef) -- TODO don't hardcode 1
                   | (name, DFunDef funDef) <- declsPairs
                   , name `Map.notMember` hofs
                   , hasHofName funDef
                   , case funTy funDef of       -- we only want to monomorphize polymorphic functions
                          TyAll {} -> True
                          _ -> False
                   ]

        hasHofName :: (Data a) => a -> Bool
        hasHofName entity = not (null [ () | TypeFromSignature name   <- universeBi entity :: [TypeBase builtins], name `Map.member` hofs ])
                         || not (null [ () | TermFromSignature name <- universeBi entity :: [TermBase builtins], name `Map.member` hofs ])


-- This really belongs to a Pretty module, but we need them here for nicer debugging anyway for now.
instance (Pretty (BuiltinTypes builtins), Pretty (FunDef builtins)) => Pretty (HofDefBody builtins) where
  pretty (HDBType defn) = "<typ>" <+> pretty defn
  pretty (HDBFun  defn) = "<fun>" <+> pretty defn

instance (Pretty (BuiltinTypes builtins), Pretty (FunDef builtins)) => Pretty (HofDef builtins) where
  pretty = pretty . hofDefBody

instance (Pretty (BuiltinTypes builtins), Pretty (FunDef builtins)) => Pretty (HOFDefs builtins) where
  pretty = align . vsep . map (\(n, d) -> pretty n <+> pretty d) . Map.toList
