{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
module Pirouette.Term.Syntax.Base where

import qualified Pirouette.Term.Syntax.SystemF as Raw
import Pirouette.Term.Syntax.Pretty.Class (Pretty)

import           Control.Arrow ((&&&))
import           Control.Monad
import           Control.Monad.State
import qualified Data.ByteString           as BS
import qualified Data.Set   as S
import           Data.List  (foldl')
import           Data.Foldable ()
import           Data.Traversable ()
import           Data.Typeable
import qualified Data.Text as T
import qualified Data.Map as M
import           Data.Data
import Data.Void

type EqOrdShowDataTypeable a = (Eq a, Ord a, Show a, Data a, Typeable a)

type LanguageConstrs lang
  = (EqOrdShowDataTypeable (BuiltinTypes lang)
    , EqOrdShowDataTypeable (BuiltinTerms lang)
    , EqOrdShowDataTypeable (Constants lang))

type PrettyLang lang = (Pretty (BuiltinTypes lang), Pretty (BuiltinTerms lang), Pretty (Constants lang))

class (Data lang, Typeable lang, LanguageConstrs lang) => LanguageDef lang where
  type BuiltinTypes lang :: *
  type BuiltinTerms lang :: *
  type Constants lang :: *

-- * Types and Type Definitions

-- |The language of types will consits of the standard polymorphic type-level lambda calculus
-- where the free variables will be of type 'TypeBase', that is, they are either a builtin type or
-- a free type.
data TypeBase lang name
  = TyBuiltin (BuiltinTypes lang)
  | TyFree    name
  deriving (Functor, Foldable, Traversable)
deriving instance (Eq name, LanguageDef lang) => Eq (TypeBase lang name)
deriving instance (Ord name, LanguageDef lang) => Ord (TypeBase lang name)
deriving instance (Show name, LanguageDef lang) => Show (TypeBase lang name)
deriving instance (Data name, LanguageDef lang) => Data (TypeBase lang name)
deriving instance (Typeable name, LanguageDef lang) => Typeable (TypeBase lang name)

-- |A Pirouette type is a 'Raw.Type' whose variables are 'TypeBase' and it has metavariables
-- of type 'meta'. If you're just using this as a library you're likely more interested in
-- 'Type'.
type TypeMeta lang meta name = Raw.Type (Raw.VarMeta meta name (TypeBase lang name))

-- |A 'Type' is a 'TypeMeta' with 'Void' passed to metavariables
type Type lang name = TypeMeta lang Void name

-- |Returns all the (free) names used by a type
typeNames :: (Ord name) => TypeMeta lang meta name -> S.Set (Raw.Arg name name)
typeNames = foldMap go
  where go :: Raw.VarMeta meta name (TypeBase lang name) -> S.Set (Raw.Arg name name)
        go (Raw.F (TyFree n)) = S.singleton (Raw.TyArg n)
        go _                  = S.empty

-- |Returns all the metavariables used by a type
typeMetas :: (Ord meta) => TypeMeta lang meta name -> S.Set meta
typeMetas = foldMap go
  where go :: Raw.VarMeta meta name (TypeBase lang name) -> S.Set meta
        go (Raw.M m) = S.singleton m
        go _         = S.empty

-- |The supported type definitions. At this point, we only support datatype definitions.
data TypeDef lang n
  = Datatype { kind          :: Raw.Kind
             , typeVariables :: [(n, Raw.Kind)]
             , destructor    :: n
             , constructors  :: [(n, Type lang n)]
             }
  deriving (Eq, Ord, Show, Data)

-- |Computes the type of the destructor from a 'TypeDef'. For example, let:
--
-- > either = Datatype
-- >   { kind          = * -> * -> *
-- >   , typeVariables = [("a", *), ("b", *)]
-- >   , destructor    = "Either_match"
-- >   , constructors  = [("Left", TyAll a b . (a -> Either a b))
-- >                     ,("Right", TyAll a b . (b -> Either a b))]
-- >   }
--
-- The type for the PlutusIR destructor of Either would be:
--
-- > TyAll a b . Either a b -> TyAll c -> (a -> c) -> (b -> c) -> c
--
destructorTypeFor :: TypeDef lang n -> Type lang n
destructorTypeFor (Datatype k vs n cs) = undefined

-- * Terms

-- |This is to 'Term', what 'TypeBase' is to 'Type'.
data TermBase lang name
  = Constant (Constants lang)
  | Builtin (BuiltinTerms lang)
  | FreeName name
  | Bottom
  deriving (Functor, Foldable, Traversable)
deriving instance (Eq name, LanguageDef lang) => Eq (TermBase lang name)
deriving instance (Ord name, LanguageDef lang) => Ord (TermBase lang name)
deriving instance (Show name, LanguageDef lang) => Show (TermBase lang name)
deriving instance (Data name, LanguageDef lang) => Data (TermBase lang name)
deriving instance (Typeable name, LanguageDef lang) => Typeable (TermBase lang name)

-- |A 'TermMeta' for a given language is a 'Raw.Term' with types being a 'Type' and
-- diambiguated free names: we're aware on whether these free names are constants,
-- builtins or refer to some definition that will require a definition map.
--
-- Moreover, there's a possibility to insert meta variables in the tree. If you're
-- a user of the library, you're most likely going to need only 'Term', which
-- have no metavariables.
type TermMeta lang meta name = Raw.Term (TypeMeta lang meta name) (Raw.VarMeta meta name (TermBase lang name))

-- |A 'Term' is a 'TermMeta' with 'Void' as the metavariable.
type Term lang name = TermMeta lang Void name

-- |Returns all the (free) names used by a term
termNames :: (Ord name) => TermMeta lang meta name -> S.Set (Raw.Arg name name)
termNames = uncurry (<>) . (foldMap go &&& Raw.termTyFoldMap typeNames)
  where go :: Raw.VarMeta meta name (TermBase lang name) -> S.Set (Raw.Arg name name)
        go (Raw.F (FreeName n)) = S.singleton (Raw.Arg n)
        go _                    = S.empty

-- |Returns all the metavariables used by a term
termMetas :: (Ord meta) => TermMeta lang meta name -> S.Set meta
termMetas = uncurry (<>) . (foldMap go &&& Raw.termTyFoldMap typeMetas)
  where go :: Raw.VarMeta meta name (TermBase lang name) -> S.Set meta
        go (Raw.M m) = S.singleton m
        go _         = S.empty

-- * Definitions

data Rec = Rec | NonRec
  deriving (Eq, Ord, Show, Data)

data FunDef lang name = FunDef
  { funIsRec :: Rec
  , funBody :: Term lang name
  , funTy :: Type lang name
  }
  deriving (Eq, Ord, Show, Data)

data Definition lang name
  = DFunDef       (FunDef lang name)
  | DConstructor  Int name
  | DDestructor   name
  | DTypeDef      (TypeDef lang name)
  deriving (Eq, Ord, Show, Data)

pattern DFunction :: Rec -> Term lang name -> Type lang name -> Definition lang name
pattern DFunction r t ty = DFunDef (FunDef r t ty)
{-# COMPLETE DFunction, DConstructor, DDestructor, DTypeDef #-}
-- TODO investigate whether this COMPLETE pragma will be still needed when we upgrade to ghc 9.0/9.2

defTermMapM :: (Monad m)
            => (Term lang name -> m (Term lang name))
            -> Definition lang name -> m (Definition lang name)
defTermMapM f (DFunction r t ty) = flip (DFunction r) ty <$> f t
defTermMapM _ (DTypeDef td)      = pure $ DTypeDef td
defTermMapM _ (DConstructor i n) = pure $ DConstructor i n
defTermMapM _ (DDestructor n)    = pure $ DDestructor n

fromTypeDef :: Definition lang name -> Maybe (TypeDef lang name)
fromTypeDef (DTypeDef d) = Just d
fromTypeDef _            = Nothing

fromTermDef :: Definition lang name -> Maybe (Term lang name)
fromTermDef (DFunction _ d _) = Just d
fromTermDef _                 = Nothing

fromDestDef :: Definition lang name -> Maybe name
fromDestDef (DDestructor d) = Just d
fromDestDef _               = Nothing

fromConstDef :: Definition lang name -> Maybe (Int, name)
fromConstDef (DConstructor i n) = Just (i , n)
fromConstDef _                  = Nothing

-- * Declarations

-- | A program will be translated into a number of term and type declarations.
type Decls lang name = M.Map name (Definition lang name)
