{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Transformations.Utils where

import Control.Arrow (first, second)
import Data.Data
import qualified Data.Map as M
import qualified Data.Text as T
import Debug.Trace
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.SystemF hiding (Arg)
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Prettyprinter hiding (Pretty, pretty)

traceDefsId :: (LanguagePretty lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
traceDefsId defs = renderSingleLineStr (pretty $ prtUODecls defs) `trace` defs

data HofDefBody lang
  = HDBType (TypeDef lang)
  | HDBFun (FunDef lang)
  deriving (Show, Eq, Ord)

data HofDef lang = HofDef
  { hofDefName :: Name,
    hofDefBody :: HofDefBody lang
  }
  deriving (Show, Eq, Ord)

type HOFDefs lang = M.Map (Namespace, Name) (HofDef lang)

findFuns ::
  LanguageBuiltins lang =>
  [((space, Name), Definition lang)] ->
  (FunDef lang -> Bool) ->
  [((space, Name), HofDef lang)]
findFuns declsPairs funPred =
  [ ((sp, name), HofDef name $ HDBFun funDef)
    | ((sp, name), DFunDef funDef) <- declsPairs,
      funPred funDef
  ]

-- | Find the types that satisfy a given predicate, additionally return all terms associated
--  with said types too: constructors and destructor.
findTypes ::
  LanguageBuiltins lang =>
  [((Namespace, Name), Definition lang)] ->
  (Name -> TypeDef lang -> Bool) ->
  [((Namespace, Name), HofDef lang)]
findTypes declsPairs tyPred =
  -- First we get the type definitions that satisfy the required predicate
  flip concatMap typeDefsSuchThat $ \(tyName, typeDef) ->
    -- Only now we add the rest of the relevant names; this is necessary because only @tyName@ belongs
    -- to 'TypeNamespace', the rest of the terms belong to 'TermNamespace'
    let spaceNames =
          (TypeNamespace, tyName) : [(TermNamespace, name) | name <- destructor typeDef : map fst (constructors typeDef)]
     in [((sp, name), HofDef tyName $ HDBType typeDef) | (sp, name) <- spaceNames]
  where
    typeDefsSuchThat = [(tyName, typeDef) | ((_, tyName), DTypeDef typeDef) <- declsPairs, tyPred tyName typeDef]

findHOFDefs ::
  forall lang.
  LanguageBuiltins lang =>
  (FunDef lang -> Bool) ->
  (Name -> TypeDef lang -> Bool) ->
  [((Namespace, Name), Definition lang)] ->
  HOFDefs lang
findHOFDefs funPred tyPred declsPairs =
  M.fromList $ findFuns declsPairs funPred' <> findTypes declsPairs tyPred'
  where
    funPred' :: FunDef lang -> Bool
    funPred' fun = funPred fun && hasHOFuns (funTy fun)
    tyPred' name typeDef = tyPred name typeDef && (hasHOFuns . snd) `any` constructors typeDef

-- | Returns whether a type has higher-order functions anywhere, directly
-- or indirectly. For instance, the type:
--
-- > Integer -> Maybe (Bool -> Bool) -> X
--
-- Has higher-order functions present nested in 'Maybe'. This current function
-- could be much better given it will also return some false-positives. For instance,
--
-- > Integer -> Const Bool (Bool -> Bool) -> X
--
-- Doesn't really have higher order functions because @Const a b = a@, but we
-- are not worrying about that now.
hasHOFuns :: (Data ann, Data ty) => AnnType ann ty -> Bool
-- (_ -> _) -> _ ...
hasHOFuns (TyFun TyFun {} _) = True
hasHOFuns (TyFun a b) = hasHOFuns a || hasHOFuns b
hasHOFuns (TyApp _ args) = hasFuns `any` args
hasHOFuns (TyLam _ _ at) = hasHOFuns at
hasHOFuns (TyAll _ _ at) = hasHOFuns at

hasFuns :: (Data ann, Data ty) => AnnType ann ty -> Bool
hasFuns (TyFun _ _) = True
hasFuns (TyApp _ args) = hasFuns `any` args
hasFuns (TyLam _ _ at) = hasFuns at
hasFuns (TyAll _ _ at) = hasFuns at

-- @Arg Kind (Type lang)@ could've been used here instead,
-- but having a distinct type seems to be a bit nicer, at least for now for hole-driven development reasons.
data FlatArgType lang
  = FlatTyArg Kind
  | FlatTermArg (Type lang)
  deriving (Show)

flattenType :: Type lang -> ([FlatArgType lang], Type lang)
flattenType ty@TyApp {} = ([], ty)
flattenType (dom `TyFun` cod) = first (FlatTermArg dom :) $ flattenType cod
flattenType (TyAll _ k ty) = first (FlatTyArg k :) $ flattenType ty
flattenType TyLam {} = error "unnormalized type"

-- * @splitArgs n args@ splits @args@ into the first @n@ type arguments and everything else.

--
-- For instance, @splitArgs 2 [Arg a, TyArg A, TyArg B, Arg b, TyArg C]@
-- yields @([A, B], [Arg a, Arg b, TyArg C])@.
splitArgs :: Int -> [SystF.Arg ty v] -> ([ty], [SystF.Arg ty v])
splitArgs 0 args = ([], args)
splitArgs n (TyArg tyArg : args) = first (tyArg :) $ splitArgs (n - 1) args
splitArgs n (arg : args) = second (arg :) $ splitArgs n args
splitArgs _ [] = error "Less args than poly args count"

-- | This is the character used to separate the type arguments and the term or type name
--  when monomorphizing. Because we need to be able to test monomorphization, this
--  is also recognized by the "Language.Pirouette.Example" as a valid part of an identifier
monoNameSep :: Char
monoNameSep = '!'

genSpecName :: (LanguageBuiltins lang) => [Type lang] -> Name -> Name
genSpecName args name = Name (nameString name <> msep <> argsToStr args) Nothing
  where
    msep = T.pack [monoNameSep]

argsToStr :: (LanguageBuiltins lang) => [Type lang] -> T.Text
argsToStr = T.intercalate msep . map f
  where
    msep = T.pack [monoNameSep]

    f (SystF.Free n `TyApp` args) =
      tyBaseString n <> if null args then mempty else "<" <> argsToStr args <> ">"
    f (SystF.TyFun a b) = f a <> "_" <> f b
    f arg = error $ "unexpected specializing arg" <> show arg

tyBaseString :: LanguageBuiltins lang => TypeBase lang -> T.Text
tyBaseString (TyBuiltin bt) = T.pack $ show bt
tyBaseString (TySig na) = nameString na

-- This really belongs to a Pretty module, but we need them here for nicer debugging anyway for now.
instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HofDefBody lang) where
  pretty (HDBType defn) = "<typ>" <+> pretty defn
  pretty (HDBFun defn) = "<fun>" <+> pretty defn

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HofDef lang) where
  pretty = pretty . hofDefBody

instance (Pretty (BuiltinTypes lang), Pretty (FunDef lang)) => Pretty (HOFDefs lang) where
  pretty = align . vsep . map (\(n, d) -> pretty n <+> pretty d) . M.toList
