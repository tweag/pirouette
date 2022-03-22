{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.Utils where

import Control.Arrow (first, second)
import Data.Data
import Data.Generics.Uniplate.Data
import qualified Data.Map as M
import qualified Data.Text as T
import Prettyprinter hiding (Pretty, pretty)

import Debug.Trace

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.SystemF hiding (Arg)
import Pirouette.Term.Builtins
import qualified Pirouette.Term.Syntax.SystemF as SystF

traceDefsId :: (PrettyLang lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
traceDefsId defs = renderSingleLineStr (pretty $ prtUODecls defs) `trace` defs

data HofDefBody lang
  = HDBType (TypeDef lang)
  | HDBFun  (FunDef lang)
  deriving (Show, Eq, Ord)

data HofDef lang = HofDef
  { hofDefName :: Name
  , hofDefBody :: HofDefBody lang
  }
  deriving (Show, Eq, Ord)

type HOFDefs lang = M.Map Name (HofDef lang)

findFuns :: LanguageBuiltins lang
         => (FunDef lang -> Bool)
         -> [(Name, Definition lang)]
         -> [(Name, HofDef lang)]
findFuns funPred declsPairs =
  [ (name, HofDef name $ HDBFun funDef)
  | (name, DFunDef funDef) <- declsPairs
  , funPred funDef
  ]

findTypes :: LanguageBuiltins lang
          => [(Name, Definition lang)]
          -> (Name -> TypeDef lang -> Bool)
          -> [(Name, HofDef lang)]
findTypes declsPairs tyPred =
  [ (name, HofDef tyName $ HDBType typeDef)
  | (tyName, DTypeDef typeDef) <- declsPairs
  , tyPred tyName typeDef
  , name <- tyName : destructor typeDef : (fst <$> constructors typeDef)
  ]

findHOFDefs :: forall lang. LanguageBuiltins lang
            => (FunDef lang -> Bool)
            -> (Name -> TypeDef lang -> Bool)
            -> [(Name, Definition lang)]
            -> HOFDefs lang
findHOFDefs funPred tyPred declsPairs = M.fromList $ findFuns funPred' declsPairs <> findTypes declsPairs tyPred'
  where
    funPred' :: FunDef lang -> Bool
    funPred' fun = funPred fun && hasHOFuns (funTy fun)
    tyPred' name typeDef = tyPred name typeDef && (hasHOFuns . snd) `any` constructors typeDef

hasHOFuns :: (Data ann, Data ty) => AnnType ann ty -> Bool
hasHOFuns ty = isHOFTy `any` [ f | f@TyFun {} <- universe ty ]

isHOFTy :: AnnType ann ty -> Bool
isHOFTy (TyFun TyFun {} _) = True
isHOFTy _ = False

-- @Arg Kind (Type lang)@ could've been used here instead,
-- but having a distinct type seems to be a bit nicer, at least for now for hole-driven development reasons.
data FlatArgType lang
  = FlatTyArg Kind
  | FlatTermArg (Type lang)
  deriving (Show)

flattenType :: Type lang -> ([FlatArgType lang], Type lang)
flattenType ty@TyApp{} = ([], ty)
flattenType (dom `TyFun` cod) = first (FlatTermArg dom :) $ flattenType cod
flattenType (TyAll _ k ty) = first (FlatTyArg k :) $ flattenType ty
flattenType TyLam{} = error "unnormalized type"

-- * @splitArgs n args@ splits @args@ into the first @n@ type arguments and everything else.
--
-- For instance, @splitArgs 2 [Arg a, TyArg A, TyArg B, Arg b, TyArg C]@
-- yields @([A, B], [Arg a, Arg b, TyArg C])@.
splitArgs :: Int -> [SystF.Arg ty v] -> ([ty], [SystF.Arg ty v])
splitArgs 0 args = ([], args)
splitArgs n (TyArg tyArg : args) = first (tyArg :) $ splitArgs (n - 1) args
splitArgs n (arg : args) = second (arg :) $ splitArgs n args
splitArgs _ [] = error "Less args than poly args count"

argsToStr :: (LanguageBuiltins lang) => [Type lang] -> T.Text
argsToStr = T.intercalate "@" . map f
  where
    f (SystF.Free (TySig n) `TyApp` []) = nameString n
    f (SystF.Free (TySig n) `TyApp` args) = nameString n <> "<" <> argsToStr args <> ">"
    f arg = error $ "unexpected specializing arg" <> show arg

-- This really belongs to a Pretty module, but we need them here for nicer debugging anyway for now.
instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HofDefBody lang) where
  pretty (HDBType defn) = "<typ>" <+> pretty defn
  pretty (HDBFun  defn) = "<fun>" <+> pretty defn

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HofDef lang) where
  pretty = pretty . hofDefBody

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HOFDefs lang) where
  pretty = align . vsep . map (\(n, d) -> pretty n <+> pretty d) . M.toList
