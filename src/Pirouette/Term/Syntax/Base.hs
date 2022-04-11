{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

-- | Provides the base syntactical elements for the languages supported by Pirouette.
--  This module /does not/ expose the underlying System F implementation. In case
--  you're interested in manipulating terms at the Systm F level make sure
--  to bring in "Pirouette.Term.Syntax.SystemF", which is meant to be
--  imported qualified.
module Pirouette.Term.Syntax.Base where

import Control.Arrow ((&&&))
import Control.Monad.Identity
import Data.Data
import Data.Map (Map)
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as Text
import Data.Void
import Optics.TH
import Pirouette.Term.Syntax.Pretty.Class
import Pirouette.Term.Syntax.Subst (shift)
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
data TypeBase lang
  = TyBuiltin (BuiltinTypes lang)
  | TySig Name

deriving instance (LanguageBuiltins lang) => Eq (TypeBase lang)

deriving instance (LanguageBuiltins lang) => Ord (TypeBase lang)

deriving instance (LanguageBuiltins lang) => Show (TypeBase lang)

deriving instance (LanguageBuiltins lang) => Data (TypeBase lang)

deriving instance (LanguageBuiltins lang) => Typeable (TypeBase lang)

-- | A Pirouette type is a 'SystF.Type' whose variables are 'TypeBase' and it has metavariables
--  of type 'meta'. If you're just using this as a library you're likely more interested in
--  'Type'.
type TypeMeta lang meta = SystF.AnnType Name (SystF.VarMeta meta Name (TypeBase lang))

-- | A 'Type' is a 'TypeMeta' with 'Void' passed to metavariables
type Type lang = TypeMeta lang Void

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
typeNames :: TypeMeta lang meta -> Set.Set (SystF.Arg Name Name)
typeNames = foldMap go
  where
    go :: SystF.VarMeta meta Name (TypeBase lang) -> Set.Set (SystF.Arg Name Name)
    go (SystF.Free (TySig n)) = Set.singleton (SystF.TyArg n)
    go _ = Set.empty

-- | Returns all the metavariables used by a type
typeMetas :: (Ord meta) => TypeMeta lang meta -> Set.Set meta
typeMetas = foldMap go
  where
    go :: SystF.VarMeta meta Name (TypeBase lang) -> Set.Set meta
    go (SystF.Meta m) = Set.singleton m
    go _ = Set.empty

-- | The supported type definitions. At this point, we only support datatype definitions.
data TypeDef lang = -- | Define a new datatype. For example:
  --
  --   > either = Datatype
  --   >   { kind          = * -> * -> *
  --   >   , typeVariables = [("a", *), ("b", *)]
  --   >   , destructor    = "Either_match"
  --   >   , constructors  = [("Left", TyAll a b . (a -> Either a b))
  --   >                     ,("Right", TyAll a b . (b -> Either a b))]
  --   >   }
  Datatype
  { kind :: SystF.Kind,
    -- | The 'typeVariables' field is here because it makes the computation of the type of destructors
    --  much easier. These type variables are declared with 'SystF.TyAll' on the types of the 'constructors'.
    typeVariables :: [(Name, SystF.Kind)],
    destructor :: Name,
    constructors :: [(Name, Type lang)]
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
--  > TyAll a b . Either a b -> TyAll c . (a -> c) -> (b -> c) -> c
destructorTypeFor :: Name -> TypeDef lang -> Type lang
destructorTypeFor tname Datatype {..} =
  foldr
    -- TyAll a b .
    (\(n, k) -> SystF.TyAll (SystF.Ann n) k)
    ( SystF.TyFun
        -- Either a b
        (SystF.Free (TySig tname) `SystF.TyApp` tyArgs)
        -- TyAll c .
        ( SystF.TyAll (SystF.Ann $ fromString "res") SystF.KStar $
            foldr
              -- (a -> c) -> (b -> c)
              (SystF.TyFun . mkConstructorType . snd)
              -- c
              res
              constructors
        )
    )
    typeVariables
  where
    arity = length typeVariables

    res = SystF.tyPure $ SystF.Bound (SystF.Ann $ fromString "res") 0

    mkConstructorType :: Type lang -> Type lang
    mkConstructorType =
      foldr (SystF.TyFun . shift 1) res
        . fst
        . SystF.tyFunArgs
        . (`SystF.tyInstantiateN` tyArgs)

    tyArgs :: [Type lang]
    tyArgs =
      zipWith
        (\(n, _) ix -> SystF.tyPure $ SystF.Bound (SystF.Ann n) (fromIntegral ix))
        typeVariables
        (reverse [0 .. arity - 1])

-- * Terms

-- | This is to 'Term', what 'TypeBase' is to 'Type'.
data TermBase lang
  = Constant (Constants lang)
  | Builtin (BuiltinTerms lang)
  | TermSig Name
  | Bottom

deriving instance (LanguageBuiltins lang) => Eq (TermBase lang)

deriving instance (LanguageBuiltins lang) => Ord (TermBase lang)

deriving instance (LanguageBuiltins lang) => Show (TermBase lang)

deriving instance (LanguageBuiltins lang) => Data (TermBase lang)

deriving instance (LanguageBuiltins lang) => Typeable (TermBase lang)

-- | A 'TermMeta' for a given lang uage is a 'SystF.Term' with types being a 'Type' and
--  diambiguated free names: we're aware on whether these free names are constants,
--  lang or refer to some definition that will require a definition map.
--
--  Moreover, there's a possibility to insert meta variables in the tree. If you're
--  a user of the library, you're most likely going to need only 'Term', which
--  have no metavariables.
type TermMeta lang meta = SystF.AnnTerm (TypeMeta lang meta) Name (SystF.VarMeta meta Name (TermBase lang))

-- | A 'Term' is a 'TermMeta' with 'Void' as the metavariable.
type Term lang = TermMeta lang Void

termMetaMapM ::
  (Monad m) =>
  (meta -> m meta') ->
  TermMeta lang meta ->
  m (TermMeta lang meta')
termMetaMapM f = SystF.termTrimapM (typeMetaMapM f) return (SystF.varMapMetaM f)

termToMeta :: Term lang -> TermMeta lang meta
termToMeta = runIdentity . termMetaMapM absurd

-- | Returns all the (free) names used by a term
termNames :: TermMeta lang meta -> Set.Set (SystF.Arg Name Name)
termNames = uncurry (<>) . (foldMap go &&& SystF.termTyFoldMap typeNames)
  where
    go :: SystF.VarMeta meta Name (TermBase lang) -> Set.Set (SystF.Arg Name Name)
    go (SystF.Free (TermSig n)) = Set.singleton (SystF.TermArg n)
    go _ = Set.empty

-- | Returns all the metavariables used by a term
termMetas :: (Ord meta) => TermMeta lang meta -> Set.Set meta
termMetas = uncurry (<>) . (foldMap go &&& SystF.termTyFoldMap typeMetas)
  where
    go :: SystF.VarMeta meta Name (TermBase lang) -> Set.Set meta
    go (SystF.Meta m) = Set.singleton m
    go _ = Set.empty

-- * Arguments and variables

type ArgMeta lang meta = SystF.Arg (TypeMeta lang meta) (TermMeta lang meta)

type Arg lang = SystF.Arg (Type lang) (Term lang)

type Var lang = SystF.Var Name (TermBase lang)

type VarMeta lang meta = SystF.VarMeta meta Name (TermBase lang)

type TyVar lang = SystF.Var Name (TypeBase lang)

type TyVarMeta lang meta = SystF.VarMeta meta Name (TypeBase lang)

-- * Definitions

data Rec = Rec | NonRec
  deriving (Eq, Ord, Show, Data)

data FunDef lang = FunDef
  { funIsRec :: Rec,
    funBody :: Term lang,
    funTy :: Type lang
  }
  deriving (Eq, Ord, Show, Data)

data Definition lang
  = DFunDef (FunDef lang)
  | DConstructor Int Name
  | DDestructor Name
  | DTypeDef (TypeDef lang)
  deriving (Eq, Ord, Show, Data)

pattern DFunction :: Rec -> Term lang -> Type lang -> Definition lang
pattern DFunction r t ty = DFunDef (FunDef r t ty)

{-# COMPLETE DFunction, DConstructor, DDestructor, DTypeDef #-}

-- TODO investigate whether this COMPLETE pragma will be still needed when we upgrade to ghc 9.0/9.2

defTermMapM ::
  (Monad m) =>
  (Term lang -> m (Term lang)) ->
  Definition lang ->
  m (Definition lang)
defTermMapM f (DFunction r t ty) = flip (DFunction r) ty <$> f t
defTermMapM _ (DTypeDef td) = pure $ DTypeDef td
defTermMapM _ (DConstructor i n) = pure $ DConstructor i n
defTermMapM _ (DDestructor n) = pure $ DDestructor n

fromTypeDef :: Definition lang -> Maybe (TypeDef lang)
fromTypeDef (DTypeDef d) = Just d
fromTypeDef _ = Nothing

fromTermDef :: Definition lang -> Maybe (Term lang)
fromTermDef (DFunction _ d _) = Just d
fromTermDef _ = Nothing

fromDestDef :: Definition lang -> Maybe Name
fromDestDef (DDestructor d) = Just d
fromDestDef _ = Nothing

fromConstDef :: Definition lang -> Maybe (Int, Name)
fromConstDef (DConstructor i n) = Just (i, n)
fromConstDef _ = Nothing

-- * Declarations

-- | A program will be translated into a number of term and type declarations.
type Decls lang = Map Name (Definition lang)

-- | A program consists in a set of declarations and a main term.
type Program lang = (Decls lang, Term lang)

-- * Language Builtins

type EqOrdShowDataTypeable a = (Eq a, Ord a, Show a, Data a, Typeable a)

type LanguageConstrs lang =
  ( EqOrdShowDataTypeable (BuiltinTypes lang),
    EqOrdShowDataTypeable (BuiltinTerms lang),
    EqOrdShowDataTypeable (Constants lang),
    Typeable lang,
    Data lang
  )

-- | Defines the builtins of a language. We distinguish the 'Constants' which are the constructors of
--  objects of the 'BuiltinTypes' and the other builtin terms (essentially functions manipulating those obects).
--  Constants can be thought of as the /literals/ of the language. Check "Language.Pirouette.Example" for
--  a simple example.
class (LanguageConstrs lang) => LanguageBuiltins lang where
  type BuiltinTypes lang :: *
  type BuiltinTerms lang :: *
  type Constants lang :: *

-- | Auxiliary constraint for pretty-printing terms of a given language.
type LanguagePretty lang =
  ( Pretty (BuiltinTypes lang),
    Pretty (BuiltinTerms lang),
    Pretty (Constants lang)
  )

-- | Auxiliary constraint grouping everything we know about @lang@.
type Language lang = (LanguageBuiltins lang, LanguagePretty lang)

-- These must go at the end because of Template Haskell restrictions

makePrisms ''Definition
makePrisms ''TypeBase
makePrisms ''TermBase
