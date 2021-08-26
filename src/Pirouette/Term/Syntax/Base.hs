{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE GADTs                #-}
module Pirouette.Term.Syntax.Base where

import qualified Pirouette.Term.Syntax.SystemF as Raw

import           PlutusCore         ( DefaultUni(..)
                                    , pattern DefaultUniList
                                    , pattern DefaultUniString
                                    , pattern DefaultUniPair )
import qualified PlutusCore        as P
import qualified PlutusCore.Pretty as P

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


-- * PIR Types

-- |Builtin Plutus Types
data PIRType
  = PIRTypeInteger
  | PIRTypeByteString
  | PIRTypeChar
  | PIRTypeUnit
  | PIRTypeBool
  | PIRTypeString
  | PIRTypeList PIRType
  | PIRTypePair PIRType PIRType
  deriving (Eq, Ord, Show, Data, Typeable)

defUniToType :: forall k (a :: k) . DefaultUni (P.Esc a) -> PIRType
defUniToType DefaultUniInteger     = PIRTypeInteger
defUniToType DefaultUniByteString  = PIRTypeByteString
defUniToType DefaultUniChar        = PIRTypeChar
defUniToType DefaultUniUnit        = PIRTypeUnit
defUniToType DefaultUniBool        = PIRTypeBool
defUniToType DefaultUniString      = PIRTypeString
defUniToType (DefaultUniList a)    = PIRTypeList (defUniToType a)
defUniToType (DefaultUniPair a b)  = PIRTypePair (defUniToType a) (defUniToType b)

-- |The language of types will consits of the standard polymorphic type-level lambda calculus
-- where the free variables will be of type 'TypeBase', that is, they are either a builtin type or
-- a free type.
data TypeBase tyname
  = TyBuiltin PIRType
  | TyFree    tyname
  deriving (Eq, Ord, Show, Data, Typeable, Functor, Foldable, Traversable)

-- |A Pirouette type, then, is a "Raw.Type" whose variables are 'TypeBase'
type Type name = Raw.Type (Raw.Var name (TypeBase name))

-- |Returns all the names used by a type
typeNames :: (Ord name) => Type name -> S.Set (Raw.Arg name name)
typeNames = foldMap go
  where go :: Raw.Var name (TypeBase name) -> S.Set (Raw.Arg name name)
        go (Raw.F (TyFree n)) = S.singleton (Raw.TyArg n)
        go _                  = S.empty

-- |For now, we only support type declarations.
data TypeDef n
  = Datatype { kind          :: Raw.Kind
             , typeVariables :: [(n, Raw.Kind)]
             , destructor    :: n
             , constructors  :: [(n, Type n)]
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
destructorTypeFor :: TypeDef n -> Type n
destructorTypeFor (Datatype k vs n cs) = undefined

-- * From PlutusIR to 'Term'
--
-- $plutustotermdoc
--
-- The translation of a 'PIR.Program' into a 'Term' happens in two phases.
-- The first phase translates a 'PIR.Program' into a @Term (Name1 ...)@ by
-- removing the let bindings and translating explicit variable names into
-- De Bruijn indicies. The second part of the translation will expand all
-- non-recursive functions and distintuish between whether a name represents
-- a recursive function, a constructor or a destructor of a datatype,
-- yielding a @Term (Name2 ...)@.

-- |Untyped Plutus Constants
data PIRConstant
  = PIRConstInteger Integer
  | PIRConstByteString BS.ByteString
  | PIRConstChar Char
  | PIRConstUnit
  | PIRConstBool Bool
  | PIRConstString String
  | PIRConstList [PIRConstant]
  | PIRConstPair PIRConstant PIRConstant
  deriving (Eq, Show, Data, Typeable)

defUniToConstant :: DefaultUni (P.Esc a) -> a -> PIRConstant
defUniToConstant DefaultUniInteger     x = PIRConstInteger x
defUniToConstant DefaultUniByteString  x = PIRConstByteString x
defUniToConstant DefaultUniChar        x = PIRConstChar x
defUniToConstant DefaultUniUnit        x = PIRConstUnit
defUniToConstant DefaultUniBool        x = PIRConstBool x
defUniToConstant DefaultUniString      x = PIRConstString x
defUniToConstant (DefaultUniList a)    x = PIRConstList (map (defUniToConstant a) x)
defUniToConstant (DefaultUniPair a b)  x = PIRConstPair (defUniToConstant a (fst x)) (defUniToConstant b (snd x))

-- |This is to 'Term', what 'TypeBase' is to 'Type'.
data PIRBase fun n
  = Constant PIRConstant
  | Builtin fun
  | Bottom
  | FreeName n
  deriving (Eq, Show, Functor, Data, Typeable)

-- |A 'Term' represents pirtla terms with disambiguated free names
type Term name fun = Raw.Term (Type name) (Raw.Var name (PIRBase fun name))

-- |Returns all the names used by a term
termNames :: (Ord name) => Term name fun -> S.Set (Raw.Arg name name)
termNames = uncurry (<>) . (foldMap go &&& Raw.termTyFoldMap typeNames)
  where go :: Raw.Var name (PIRBase fun name) -> S.Set (Raw.Arg name name)
        go (Raw.F (FreeName n)) = S.singleton (Raw.Arg n)
        go _                    = S.empty

data Rec = Rec | NonRec
  deriving (Eq , Show)

data Definition n fun
  = DFunction Rec (Term n fun) (Type n)
  | DConstructor  Int n
  | DDestructor   n
  | DTypeDef      (TypeDef n)
  deriving (Eq, Show)

defTermMapM :: (Monad m)
            => (Term n fun -> m (Term n fun'))
            -> Definition n fun -> m (Definition n fun')
defTermMapM f (DFunction r t ty) = flip (DFunction r) ty <$> f t
defTermMapM _ (DTypeDef td)      = pure $ DTypeDef td
defTermMapM _ (DConstructor i n) = pure $ DConstructor i n
defTermMapM _ (DDestructor n)    = pure $ DDestructor n

fromTypeDef :: Definition n fun -> Maybe (TypeDef n)
fromTypeDef (DTypeDef d) = Just d
fromTypeDef _            = Nothing

fromTermDef :: Definition n fun -> Maybe (Term n fun)
fromTermDef (DFunction _ d _) = Just d
fromTermDef _                 = Nothing

fromDestDef :: Definition n fun -> Maybe n
fromDestDef (DDestructor d) = Just d
fromDestDef _               = Nothing

fromConstDef :: Definition n fun -> Maybe (Int, n)
fromConstDef (DConstructor i n) = Just (i , n)
fromConstDef _                  = Nothing

-- * Declarations

-- | A PlutusIR program will be translated into a number of term and type declarations.
-- Because the translation happens in two phases, we also have 'Decls'' and 'Decls'.
type Decls name fun = M.Map name (Definition name fun)
