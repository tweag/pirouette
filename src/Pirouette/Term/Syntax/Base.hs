{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Pirouette.Term.Syntax.Base where

import qualified Pirouette.Term.Syntax.SystemF as Raw
import Pirouette.Term.Syntax.Pretty.Class

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
import Data.String
import Control.Monad.Identity

type EqOrdShowDataTypeable a = (Eq a, Ord a, Show a, Data a, Typeable a)

type LanguageConstrs builtins
  = (EqOrdShowDataTypeable (BuiltinTypes builtins)
    , EqOrdShowDataTypeable (BuiltinTerms builtins)
    , EqOrdShowDataTypeable (Constants builtins))

type PrettyLang builtins
  = ( Pretty (BuiltinTypes builtins),
      Pretty (BuiltinTerms builtins),
      Pretty (Constants builtins))

-- The builtins of a language.
-- We distinguish the `Constants` which are the constructors of objects of the `BuiltinTypes`
-- and the other builtin objects (essentially functions manipulating those obects).
class (Data builtins, Typeable builtins, LanguageConstrs builtins) => LanguageBuiltins builtins where
  type BuiltinTypes builtins :: *
  type BuiltinTerms builtins :: *
  type Constants builtins :: *

-- * Names

-- |Our own name type. This is useful because since we're producing code that
-- is supposed to be humanly readable, we might want to remove the 'nameUnique'
-- part of non-ambiguous names.
data Name = Name { nameString :: T.Text, nameUnique :: Maybe Int }
  deriving (Eq , Ord, Data, Typeable)

-- |We'll just define a 'TyName' synonym to keep our Haskell type-signatures
-- more organized.
type TyName = Name

instance Show Name where
  show (Name str i) = T.unpack str <> maybe mempty show i

instance IsString Name where
  fromString = flip Name Nothing . T.pack

instance Pretty Name where
  pretty (Name str i) = pretty str <> maybe mempty pretty i

class ToName v where
  toName :: v -> Name

-- * Types and Type Definitions

-- |The builtinsuage of types will consits of the standard polymorphic type-level lambda calculus
-- where the free variables will be of type 'TypeBase', that is, they are either a builtin type or
-- a free type.
data TypeFree builtins
  = TyBuiltin (BuiltinTypes builtins)
  | TypeFromSignature Name
deriving instance (LanguageBuiltins builtins) => Eq (TypeFree builtins)
deriving instance (LanguageBuiltins builtins) => Ord (TypeFree builtins)
deriving instance (LanguageBuiltins builtins) => Show (TypeFree builtins)
deriving instance (LanguageBuiltins builtins) => Data (TypeFree builtins)
deriving instance (LanguageBuiltins builtins) => Typeable (TypeFree builtins)

-- |A Pirouette type is a 'Raw.Type' whose variables are 'TypeBase' and it has metavariables
-- of type 'meta'. If you're just using this as a library you're likely more interested in
-- 'Type'.
type TypeMeta builtins meta = Raw.AnnType Name (Raw.VarMeta meta Name (TypeFree builtins))

-- |A 'Type' is a 'TypeMeta' with 'Void' passed to metavariables
type Type builtins = TypeMeta builtins Void

typeMetaMapM :: (Monad m) => (meta -> m meta')
                -> TypeMeta lang meta
                -> m (TypeMeta lang meta')
typeMetaMapM f = Raw.tyBimapM return (Raw.varMapMetaM f)

typeToMeta :: Type lang -> TypeMeta lang meta
typeToMeta = runIdentity . typeMetaMapM absurd

typeFromMeta :: TypeMeta lang meta -> Type lang
typeFromMeta = runIdentity . typeMetaMapM (const $ error "Type with metavariables")

-- |Returns all the (free) names used by a type
typeNames :: TypeMeta builtins meta -> S.Set (Raw.Arg Name Name)
typeNames = foldMap go
  where go :: Raw.VarMeta meta Name (TypeFree builtins) -> S.Set (Raw.Arg Name Name)
        go (Raw.Free (TypeFromSignature n)) = S.singleton (Raw.TyArg n)
        go _                  = S.empty

-- |Returns all the metavariables used by a type
typeMetas :: (Ord meta) => TypeMeta builtins meta -> S.Set meta
typeMetas = foldMap go
  where go :: Raw.VarMeta meta Name (TypeFree builtins) -> S.Set meta
        go (Raw.Meta m) = S.singleton m
        go _         = S.empty

-- |The supported type definitions. At this point, we only support datatype definitions.
data TypeDef builtins
  = Datatype { kind          :: Raw.Kind
             , typeVariables :: [(Name, Raw.Kind)]
             , destructor    :: Name
             , constructors  :: [(Name, Type builtins)]
             }
  deriving (Eq, Show)

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
destructorTypeFor :: TypeDef builtins -> Type builtins
destructorTypeFor (Datatype k vs n cs) = undefined

-- * Terms

-- |This is to 'Term', what 'TypeFree' is to 'Type'.
data TermFree builtins
  = Constant (Constants builtins)
  | Builtin (BuiltinTerms builtins)
  | TermFromSignature Name
  | Bottom
deriving instance (LanguageBuiltins builtins) => Eq (TermFree builtins)
deriving instance (LanguageBuiltins builtins) => Ord (TermFree builtins)
deriving instance (LanguageBuiltins builtins) => Show (TermFree builtins)
deriving instance (LanguageBuiltins builtins) => Data (TermFree builtins)
deriving instance (LanguageBuiltins builtins) => Typeable (TermFree builtins)

-- |A 'TermMeta' for a given builtins uage is a 'Raw.Term' with types being a 'Type' and
-- diambiguated free names: we're aware on whether these free names are constants,
-- builtins or refer to some definition that will require a definition map.
--
-- Moreover, there's a possibility to insert meta variables in the tree. If you're
-- a user of the library, you're most likely going to need only 'Term', which
-- have no metavariables.
type TermMeta builtins meta = Raw.AnnTerm (TypeMeta builtins meta) Name (Raw.VarMeta meta Name (TermFree builtins))

-- |A 'Term' is a 'TermMeta' with 'Void' as the metavariable.
type Term builtins = TermMeta builtins Void

termMetaMapM :: (Monad m) => (meta -> m meta')
                -> TermMeta lang meta
                -> m (TermMeta lang meta')
termMetaMapM f = Raw.termTrimapM (typeMetaMapM f) return (Raw.varMapMetaM f)

termToMeta :: Term builtins -> TermMeta builtins meta
termToMeta = runIdentity . termMetaMapM absurd

-- |Returns all the (free) names used by a term
termNames :: TermMeta builtins meta -> S.Set (Raw.Arg Name Name)
termNames = uncurry (<>) . (foldMap go &&& Raw.termTyFoldMap typeNames)
  where go :: Raw.VarMeta meta Name (TermFree builtins) -> S.Set (Raw.Arg Name Name)
        go (Raw.Free (TermFromSignature n)) = S.singleton (Raw.TermArg n)
        go _                    = S.empty

-- |Returns all the metavariables used by a term
termMetas :: (Ord meta) => TermMeta builtins meta -> S.Set meta
termMetas = uncurry (<>) . (foldMap go &&& Raw.termTyFoldMap typeMetas)
  where go :: Raw.VarMeta meta Name (TermFree builtins) -> S.Set meta
        go (Raw.Meta m) = S.singleton m
        go _         = S.empty

-- * Arguments and variables


type ArgMeta builtins meta = Raw.Arg (TypeMeta builtins meta) (TermMeta builtins meta)
type Arg builtins = Raw.Arg (Type builtins) (Term builtins)

type Var builtins = Raw.Var Name (TermFree builtins)
type VarMeta builtins meta = Raw.VarMeta meta Name (TermFree builtins)

type TyVar builtins = Raw.Var Name (TypeFree builtins)
type TyVarMeta builtins meta = Raw.VarMeta meta Name (TypeFree builtins)

-- * Definitions

data Rec = Rec | NonRec
  deriving (Eq , Show)

data Definition builtins
  = DFunction Rec (Term builtins) (Type builtins)
  | DConstructor  Int Name
  | DDestructor   Name
  | DTypeDef      (TypeDef builtins)
  deriving (Eq, Show)

defTermMapM :: (Monad m)
            => (Term builtins -> m (Term builtins))
            -> Definition builtins -> m (Definition builtins)
defTermMapM f (DFunction r t ty) = flip (DFunction r) ty <$> f t
defTermMapM _ (DTypeDef td)      = pure $ DTypeDef td
defTermMapM _ (DConstructor i n) = pure $ DConstructor i n
defTermMapM _ (DDestructor n)    = pure $ DDestructor n

fromTypeDef :: Definition builtins -> Maybe (TypeDef builtins)
fromTypeDef (DTypeDef d) = Just d
fromTypeDef _            = Nothing

fromTermDef :: Definition builtins -> Maybe (Term builtins)
fromTermDef (DFunction _ d _) = Just d
fromTermDef _                 = Nothing

fromDestDef :: Definition builtins -> Maybe Name
fromDestDef (DDestructor d) = Just d
fromDestDef _               = Nothing

fromConstDef :: Definition builtins -> Maybe (Int, Name)
fromConstDef (DConstructor i n) = Just (i , n)
fromConstDef _                  = Nothing

-- * Declarations

-- | A program will be translated into a number of term and type declarations.
type Decls builtins = M.Map Name (Definition builtins)
