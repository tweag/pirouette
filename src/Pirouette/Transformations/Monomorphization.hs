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

import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Bifunctor
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.String
import qualified Data.Text as T
import Data.Void
import Prettyprinter hiding (Pretty, pretty)

import Debug.Trace

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.Pretty
import Pirouette.Term.Syntax.Subst
import Pirouette.Term.Syntax.SystemF

traceDefsId :: (PrettyLang lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
traceDefsId defs = renderSingleLineStr (pretty $ prtUODecls defs) `trace` defs

monomorphize :: forall lang. (PrettyLang lang, Pretty (FunDef lang Name), LanguageDef lang)
             => PrtUnorderedDefs lang
             -> PrtUnorderedDefs lang
monomorphize defs0 = traceDefsId (prune $ go mempty defs0)
  where
    hofDefsRoots = findHOFDefs $ prtUODecls defs0
    hofDefs = hofsClosure (prtUODecls defs0) hofDefsRoots

    go :: S.Set (SpecRequest lang) -> PrtUnorderedDefs lang -> PrtUnorderedDefs lang
    go prevOrders defs
      | M.null newDefs && defs == defs' = defs'
      | otherwise = -- renderSingleLineStr (pretty (head $ M.elems $ head $ executeSpecRequest <$> specOrders)) `trace`
                    go (prevOrders <> S.fromList newOrders) $ addDecls newDefs defs'
      where
        (defs', specOrders) = runWriter $ transformBiM (specFunApp hofDefs :: SpecFunApp lang) defs
                                      >>= transformBiM (specTyApp  hofDefs :: SpecTyApp  lang)
        newOrders = filter (`S.notMember` prevOrders) specOrders
        newDefs = foldMap executeSpecRequest newOrders

    prune :: PrtUnorderedDefs lang -> PrtUnorderedDefs lang
    prune defs = defs { prtUODecls = M.filterWithKey (\n _ -> n `M.notMember` hofDefs) $ prtUODecls defs }

data SpecRequest lang = SpecRequest
  { origDef :: HofDef lang
  , specArgs :: [PrtType lang]
  }
  deriving (Show, Eq, Ord)

type SpecFunApp lang = forall m. MonadWriter [SpecRequest lang] m => TermMeta lang Void Name -> m (TermMeta lang Void Name)
type SpecTyApp  lang = forall m. MonadWriter [SpecRequest lang] m => TypeMeta lang Void Name -> m (TypeMeta lang Void Name)

executeSpecRequest :: (LanguageDef lang) => SpecRequest lang -> Decls lang Name
executeSpecRequest SpecRequest {origDef = HofDef{..}, ..} = M.fromList $
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

specFunApp :: forall lang. (LanguageDef lang) => HOFDefs lang -> SpecFunApp lang
specFunApp hofDefs (App (F (FreeName name)) args)
  | Just someDef <- name `M.lookup` hofDefs    -- TODO should just the nameString be compared?
  , all isSpecArg $ take (hofPolyVarsCount someDef) tyArgs = do
    let (specArgs, remainingArgs) = splitArgs (hofPolyVarsCount someDef) args
        speccedName = genSpecName specArgs name
    tell $ pure $ SpecRequest someDef specArgs
    pure $ F (FreeName speccedName) `App` remainingArgs
  where
    tyArgs = mapMaybe fromTyArg args
    splitArgs 0 args = ([], args)
    splitArgs n (TyArg tyArg : args) = first (tyArg :) $ splitArgs (n - 1) args
    splitArgs n (arg : args) = second (arg :) $ splitArgs n args
    splitArgs _ [] = error "Less args than poly args count"
specFunApp _ x = pure x

specTyApp :: (LanguageDef lang) => HOFDefs lang -> SpecTyApp lang
specTyApp hofDefs (TyApp (F (TyFree name)) tyArgs)
  | Just someDef <- name `M.lookup` hofDefs
  , all isSpecArg $ take (hofPolyVarsCount someDef) tyArgs = do
    let (specArgs, remainingArgs) = splitAt (hofPolyVarsCount someDef) tyArgs
        speccedName = genSpecName specArgs name
    tell $ pure $ SpecRequest someDef specArgs
    pure $ F (TyFree speccedName) `TyApp` remainingArgs
specTyApp _ x = pure x

argsToStr :: (LanguageDef lang) => [PrtType lang] -> T.Text
argsToStr = T.intercalate "@" . map f
  where
    f (F (TyFree n) `TyApp` []) = nameString n
    f (F (TyFree n) `TyApp` args) = nameString n <> "<" <> argsToStr args <> ">"
    f arg = error $ "unexpected specializing arg" <> show arg

genSpecName :: (LanguageDef lang) => [PrtType lang] -> Name -> Name
genSpecName args name = Name (nameString name <> "@" <> argsToStr args) Nothing

-- A type argument is fully specialized if it has no bound variables
isSpecArg :: forall lang. LanguageDef lang => PrtType lang -> Bool
isSpecArg arg = null bounds
  where
    bounds :: [VarMeta Void Name (TypeBase lang Name)]
    bounds = filter (isJust . isBound) $ universeBi arg

-- Types can't depend on terms, so it's safe to move all type applications to the front.
-- Also, this function is obviously broken right now.
reorderAppTys :: forall lang. LanguageDef lang
              => PrtUnorderedDefs lang
              -> PrtUnorderedDefs lang
reorderAppTys = transformBi f . error "this is currently broken"
  where
    f :: TermMeta lang Void Name -> TermMeta lang Void Name
    f (App vm args) = App vm (reorder args)
    f t = t

    -- TODO fix de Bruijn indices
    reorder = uncurry (<>) . partition isTyArg

data HofDefBody lang
  = HDBType (TypeDef lang Name)
  | HDBFun  (FunDef lang Name)
  deriving (Show, Eq, Ord)

data HofDef lang = HofDef
  { hofDefName :: Name
  , hofPolyVarsCount :: Int
  , hofDefBody :: HofDefBody lang
  }
  deriving (Show, Eq, Ord)
-- TODO the above definition shouldn't have hofPolyVarsCount as the _count_,
-- since the HOF-involved type args aren't necessarily at the front of the application.
-- A smarter approach would be to keep a list of type variables need to be monomorphized,
-- but this kludge together with hardcoding it to be `1` gets us far enough
-- to work with SMT on some realistic examples.

type HOFDefs lang = M.Map Name (HofDef lang)

-- Returns the definitions containing higher-order functions,
-- be it functions or types.
--
-- The returned Map maps any name that contains higher-order stuff.
-- In particular, for a type it contains the type itself as well as
-- the type's constructors and destructor.
findHOFDefs :: LanguageDef lang => Decls lang Name -> HOFDefs lang
findHOFDefs decls = M.fromList $ hofTypes <> hofFuns
  where
    hofTypes = mkTypeHofDefs declsPairs $ \_ typeDef -> (hasHOFuns . snd) `any` constructors typeDef
    hofFuns = [ (name, HofDef name 1 $ HDBFun funDef)  -- TODO don't hardcode 1
              | (name, DFunDef funDef) <- declsPairs
              , hasHOFuns $ funTy funDef
              ]
    declsPairs = M.toList decls

mkTypeHofDefs :: LanguageDef lang
              => [(Name, Definition lang Name)]
              -> (Name -> TypeDef lang Name -> Bool)
              -> [(Name, HofDef lang)]
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


hofsClosure :: forall lang. (LanguageDef lang, PrettyLang lang) => Decls lang Name -> HOFDefs lang -> HOFDefs lang
hofsClosure decls = go
  where
    declsPairs = M.toList decls

    go hofs
      | hofs == hofs' = hofs
      | otherwise = hofs'
      where
        hofs' = hofs <> M.fromList (hofTypes' <> hofFuns')
        hofTypes' = mkTypeHofDefs declsPairs $ \tyName typeDef -> tyName `M.notMember` hofs
                                                               && hasHofName typeDef
        hofFuns' = [ (name, HofDef name 1 $ HDBFun funDef) -- TODO don't hardcode 1
                   | (name, DFunDef funDef) <- declsPairs
                   , name `M.notMember` hofs
                   , hasHofName funDef
                   , case funTy funDef of       -- we only want to monomorphize polymorphic functions
                          TyAll {} -> True
                          _ -> False
                   ]

        hasHofName :: (Data a) => a -> Bool
        hasHofName entity = not (null [ () | TyFree name   <- universeBi entity :: [TypeBase lang Name], name `M.member` hofs ])
                         || not (null [ () | FreeName name <- universeBi entity :: [TermBase lang Name], name `M.member` hofs ])


-- This really belongs to a Pretty module, but we need them here for nicer debugging anyway for now.
instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang Name)) => Pretty (HofDefBody lang) where
  pretty (HDBType defn) = "<typ>" <+> pretty defn
  pretty (HDBFun  defn) = "<fun>" <+> pretty defn

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang Name)) => Pretty (HofDef lang) where
  pretty = pretty . hofDefBody

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang Name)) => Pretty (HOFDefs lang) where
  pretty = align . vsep . map (\(n, d) -> pretty n <+> pretty d) . M.toList
