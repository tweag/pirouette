{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Pirouette.Term.Syntax.Base where

import Control.Arrow ((&&&))
import Control.Monad.Identity
import Data.Data
import Data.Map (Map)
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as Text
import Data.Typeable
import Data.Void
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax.Pretty.Class
import qualified Pirouette.Term.Syntax.SystemF as SystF

-- * Names

-- | Our own name type. This is useful because since we're producing code that
--  is supposed to be humanly readable, we might want to remove the 'nameUnique'
--  part of non-ambiguous names.
data Name = Name {nameString :: Text.Text, nameUnique :: Maybe Int}
  deriving (Eq, Ord, Data, Typeable)

-- | We'll just define a 'TyName' synonym to keep our Haskell type-signatures
--  more organized.
type TyName = Name

instance Show Name where
  show (Name str i) = Text.unpack str <> maybe mempty show i

instance IsString Name where
  fromString = flip Name Nothing . Text.pack

instance Pretty Name where
  pretty (Name str i) = pretty str <> maybe mempty pretty i

class ToName v where
  toName :: v -> Name

-- * Types and Type Definitions

-- | The type system we are interested in is standard polymorphic type-level lambda calculus
--  where the free variables will be of type 'TypeBase', that is, they are either a builtin type or
--  a type name that refers to some type defined in our context and possessing a signature.
data TypeBase builtins
  = TyBuiltin (BuiltinTypes builtins)
  | TySig Name

deriving instance (LanguageBuiltins builtins) => Eq (TypeBase builtins)

deriving instance (LanguageBuiltins builtins) => Ord (TypeBase builtins)

deriving instance (LanguageBuiltins builtins) => Show (TypeBase builtins)

deriving instance (LanguageBuiltins builtins) => Data (TypeBase builtins)

deriving instance (LanguageBuiltins builtins) => Typeable (TypeBase builtins)

-- | A Pirouette type is a 'SystF.Type' whose variables are 'TypeBase' and it has metavariables
--  of type 'meta'. If you're just using this as a library you're likely more interested in
--  'Type'.
type TypeMeta builtins meta = SystF.AnnType Name (SystF.VarMeta meta Name (TypeBase builtins))

-- | A 'Type' is a 'TypeMeta' with 'Void' passed to metavariables
type Type builtins = TypeMeta builtins Void

typeMetaMapM ::
  (Monad m) =>
  (meta -> m meta') ->
  TypeMeta lang meta ->
  m (TypeMeta lang meta')
typeMetaMapM f = SystF.tyBimapM return (SystF.varMapMetaM f)

typeToMeta :: Type lang -> TypeMeta lang meta
typeToMeta = runIdentity . typeMetaMapM absurd

typeFromMeta :: TypeMeta lang meta -> Type lang
typeFromMeta = runIdentity . typeMetaMapM (const $ error "Type with metavariables")

-- | Returns all the (free) names used by a type
typeNames :: TypeMeta builtins meta -> Set.Set (SystF.Arg Name Name)
typeNames = foldMap go
  where
    go :: SystF.VarMeta meta Name (TypeBase builtins) -> Set.Set (SystF.Arg Name Name)
    go (SystF.Free (TySig n)) = Set.singleton (SystF.TyArg n)
    go _ = Set.empty

-- | Returns all the metavariables used by a type
typeMetas :: (Ord meta) => TypeMeta builtins meta -> Set.Set meta
typeMetas = foldMap go
  where
    go :: SystF.VarMeta meta Name (TypeBase builtins) -> Set.Set meta
    go (SystF.Meta m) = Set.singleton m
    go _ = Set.empty

-- | The supported type definitions. At this point, we only support datatype definitions.
data TypeDef builtins = Datatype
  { kind :: SystF.Kind,
    typeVariables :: [(Name, SystF.Kind)],
    destructor :: Name,
    constructors :: [(Name, Type builtins)]
  }
  deriving (Eq, Ord, Show, Data)

-- | Computes the type of the destructor from a 'TypeDef'. For example, let:
--
--  > either = Datatype
--  >   { kind          = * -> * -> *
--  >   , typeVariables = [("a", *), ("b", *)]
--  >   , destructor    = "Either_match"
--  >   , constructors  = [("Left", TyAll a b . (a -> Either a b))
--  >                     ,("Right", TyAll a b . (b -> Either a b))]
--  >   }
--
--  The type for the PlutusIR destructor of Either would be:
--
--  > TyAll a b . Either a b -> TyAll c -> (a -> c) -> (b -> c) -> c
destructorTypeFor :: TypeDef builtins -> Type builtins
destructorTypeFor Datatype {} = undefined

-- * Terms

-- | This is to 'Term', what 'TypeBase' is to 'Type'.
data TermBase builtins
  = Constant (Constants builtins)
  | Builtin (BuiltinTerms builtins)
  | TermSig Name
  | Bottom

deriving instance (LanguageBuiltins builtins) => Eq (TermBase builtins)

deriving instance (LanguageBuiltins builtins) => Ord (TermBase builtins)

deriving instance (LanguageBuiltins builtins) => Show (TermBase builtins)

deriving instance (LanguageBuiltins builtins) => Data (TermBase builtins)

deriving instance (LanguageBuiltins builtins) => Typeable (TermBase builtins)

-- | A 'TermMeta' for a given builtins uage is a 'SystF.Term' with types being a 'Type' and
--  diambiguated free names: we're aware on whether these free names are constants,
--  builtins or refer to some definition that will require a definition map.
--
--  Moreover, there's a possibility to insert meta variables in the tree. If you're
--  a user of the library, you're most likely going to need only 'Term', which
--  have no metavariables.
type TermMeta builtins meta = SystF.AnnTerm (TypeMeta builtins meta) Name (SystF.VarMeta meta Name (TermBase builtins))

-- | A 'Term' is a 'TermMeta' with 'Void' as the metavariable.
type Term builtins = TermMeta builtins Void

termMetaMapM ::
  (Monad m) =>
  (meta -> m meta') ->
  TermMeta lang meta ->
  m (TermMeta lang meta')
termMetaMapM f = SystF.termTrimapM (typeMetaMapM f) return (SystF.varMapMetaM f)

termToMeta :: Term builtins -> TermMeta builtins meta
termToMeta = runIdentity . termMetaMapM absurd

-- | Returns all the (free) names used by a term
termNames :: TermMeta builtins meta -> Set.Set (SystF.Arg Name Name)
termNames = uncurry (<>) . (foldMap go &&& SystF.termTyFoldMap typeNames)
  where
    go :: SystF.VarMeta meta Name (TermBase builtins) -> Set.Set (SystF.Arg Name Name)
    go (SystF.Free (TermSig n)) = Set.singleton (SystF.TermArg n)
    go _ = Set.empty

-- | Returns all the metavariables used by a term
termMetas :: (Ord meta) => TermMeta builtins meta -> Set.Set meta
termMetas = uncurry (<>) . (foldMap go &&& SystF.termTyFoldMap typeMetas)
  where
    go :: SystF.VarMeta meta Name (TermBase builtins) -> Set.Set meta
    go (SystF.Meta m) = Set.singleton m
    go _ = Set.empty

-- * Arguments and variables

type ArgMeta builtins meta = SystF.Arg (TypeMeta builtins meta) (TermMeta builtins meta)

type Arg builtins = SystF.Arg (Type builtins) (Term builtins)

type Var builtins = SystF.Var Name (TermBase builtins)

type VarMeta builtins meta = SystF.VarMeta meta Name (TermBase builtins)

type TyVar builtins = SystF.Var Name (TypeBase builtins)

type TyVarMeta builtins meta = SystF.VarMeta meta Name (TypeBase builtins)

-- * Definitions

data Rec = Rec | NonRec
  deriving (Eq, Ord, Show, Data)

data FunDef builtins = FunDef
  { funIsRec :: Rec,
    funBody :: Term builtins,
    funTy :: Type builtins
  }
  deriving (Eq, Ord, Show, Data)

data Definition builtins
  = DFunDef (FunDef builtins)
  | DConstructor Int Name
  | DDestructor Name
  | DTypeDef (TypeDef builtins)
  deriving (Eq, Ord, Show, Data)

pattern DFunction :: Rec -> Term builtins -> Type builtins -> Definition builtins
pattern DFunction r t ty = DFunDef (FunDef r t ty)

{-# COMPLETE DFunction, DConstructor, DDestructor, DTypeDef #-}

-- TODO investigate whether this COMPLETE pragma will be still needed when we upgrade to ghc 9.0/9.2

defTermMapM ::
  (Monad m) =>
  (Term builtins -> m (Term builtins)) ->
  Definition builtins ->
  m (Definition builtins)
defTermMapM f (DFunction r t ty) = flip (DFunction r) ty <$> f t
defTermMapM _ (DTypeDef td) = pure $ DTypeDef td
defTermMapM _ (DConstructor i n) = pure $ DConstructor i n
defTermMapM _ (DDestructor n) = pure $ DDestructor n

fromTypeDef :: Definition builtins -> Maybe (TypeDef builtins)
fromTypeDef (DTypeDef d) = Just d
fromTypeDef _ = Nothing

fromTermDef :: Definition builtins -> Maybe (Term builtins)
fromTermDef (DFunction _ d _) = Just d
fromTermDef _ = Nothing

fromDestDef :: Definition builtins -> Maybe Name
fromDestDef (DDestructor d) = Just d
fromDestDef _ = Nothing

fromConstDef :: Definition builtins -> Maybe (Int, Name)
fromConstDef (DConstructor i n) = Just (i, n)
fromConstDef _ = Nothing

-- * Declarations

-- | A program will be translated into a number of term and type declarations.
type Decls builtins = Map Name (Definition builtins)
