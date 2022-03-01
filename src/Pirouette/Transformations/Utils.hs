{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.Utils where

import Data.Data
import Data.Generics.Uniplate.Data
import qualified Data.Map as M
import qualified Data.Text as T
import Prettyprinter hiding (Pretty, pretty)

import Debug.Trace

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF

traceDefsId :: (PrettyLang lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
traceDefsId defs = renderSingleLineStr (pretty $ prtUODecls defs) `trace` defs

data HofDefBody lang
  = HDBType (TypeDef lang Name)
  | HDBFun  (FunDef lang Name)
  deriving (Show, Eq, Ord)

data HofDef lang = HofDef
  { hofDefName :: Name
  , hofDefBody :: HofDefBody lang
  }
  deriving (Show, Eq, Ord)

type HOFDefs lang = M.Map Name (HofDef lang)

findFuns :: LanguageDef lang
         => (forall ann. Data ann => FunDef lang ann -> Bool)
         -> [(Name, Definition lang Name)]
         -> [(Name, HofDef lang)]
findFuns pred declsPairs =
  [ (name, HofDef name $ HDBFun funDef)
  | (name, DFunDef funDef) <- declsPairs
  , pred funDef
  ]

findTypes :: LanguageDef lang
          => [(Name, Definition lang Name)]
          -> (Name -> TypeDef lang Name -> Bool)
          -> [(Name, HofDef lang)]
findTypes declsPairs pred =
  [ (name, HofDef tyName $ HDBType typeDef)
  | (tyName, DTypeDef typeDef) <- declsPairs
  , pred tyName typeDef
  , name <- tyName : destructor typeDef : (fst <$> constructors typeDef)
  ]

findHOFDefs :: forall lang. LanguageDef lang
            => (forall ann. Data ann => FunDef lang ann -> Bool)
            -> (Name -> TypeDef lang Name -> Bool)
            -> [(Name, Definition lang Name)]
            -> HOFDefs lang
findHOFDefs funPred tyPred declsPairs = M.fromList $ findFuns funPred' declsPairs <> findTypes declsPairs tyPred'
  where
    funPred' :: forall ann. Data ann => FunDef lang ann -> Bool
    funPred' fun = funPred fun && hasHOFuns (funTy fun)
    tyPred' name typeDef = tyPred name typeDef && (hasHOFuns . snd) `any` constructors typeDef

hasHOFuns :: (Data ann, Data ty) => AnnType ann ty -> Bool
hasHOFuns ty = isHOFTy `any` [ f | f@TyFun {} <- universe ty ]

isHOFTy :: AnnType ann ty -> Bool
isHOFTy (TyFun TyFun {} _) = True
isHOFTy _ = False

argsToStr :: (LanguageDef lang) => [PrtType lang] -> T.Text
argsToStr = T.intercalate "@" . map f
  where
    f (F (TyFree n) `TyApp` []) = nameString n
    f (F (TyFree n) `TyApp` args) = nameString n <> "<" <> argsToStr args <> ">"
    f arg = error $ "unexpected specializing arg" <> show arg

-- This really belongs to a Pretty module, but we need them here for nicer debugging anyway for now.
instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang Name)) => Pretty (HofDefBody lang) where
  pretty (HDBType defn) = "<typ>" <+> pretty defn
  pretty (HDBFun  defn) = "<fun>" <+> pretty defn

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang Name)) => Pretty (HofDef lang) where
  pretty = pretty . hofDefBody

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang Name)) => Pretty (HOFDefs lang) where
  pretty = align . vsep . map (\(n, d) -> pretty n <+> pretty d) . M.toList
