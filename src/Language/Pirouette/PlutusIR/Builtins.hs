{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveLift #-}

-- | This module declares 'PlutusIR' as a supported language, instantiates all the
--  necessary bits for using the facilities from "Pirouette.Term.Syntax" and provides
--  a translation function 'trProgram' to translate a plutusIR program into a 'PrtTerm'
--  and a map of definitions.
module Language.Pirouette.PlutusIR.Builtins where

import qualified Data.ByteString as BS
import Data.Data
import qualified Data.Text as T
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax.Pretty.Class
import PlutusCore
  ( DefaultUni (..),
    pattern DefaultUniList,
    pattern DefaultUniPair,
    pattern DefaultUniString,
  )
import Language.Haskell.TH.Syntax (Lift)
import qualified PlutusCore as P
import qualified PlutusCore.Data as P
import Prettyprinter hiding (Pretty, pretty)

-- * Declaring the builtins of PlutusIR.

-- | Defining the 'PlutusIR' as a language, which contains a set of builtin (types and terms)
-- and constants.
data BuiltinsOfPIR
  deriving (Data, Typeable)

deriving instance Data P.DefaultFun

deriving instance Lift P.DefaultFun

deriving instance Data P.Data

deriving instance Lift P.Data

instance LanguageBuiltins BuiltinsOfPIR where
  type BuiltinTypes BuiltinsOfPIR = PIRBuiltinType
  type BuiltinTerms BuiltinsOfPIR = P.DefaultFun
  type Constants BuiltinsOfPIR = PIRConstant

-- | Builtin Plutus Types
data PIRBuiltinType
  = PIRTypeInteger
  | PIRTypeByteString
  | PIRTypeUnit
  | PIRTypeBool
  | PIRTypeString
  | PIRTypeData
  | PIRTypeList (Maybe PIRBuiltinType)
  | PIRTypePair (Maybe PIRBuiltinType) (Maybe PIRBuiltinType)
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

defUniToType :: forall k (a :: k). DefaultUni (P.Esc a) -> PIRBuiltinType
defUniToType DefaultUniInteger = PIRTypeInteger
defUniToType DefaultUniByteString = PIRTypeByteString
defUniToType DefaultUniUnit = PIRTypeUnit
defUniToType DefaultUniBool = PIRTypeBool
defUniToType DefaultUniString = PIRTypeString
defUniToType DefaultUniData = PIRTypeData
defUniToType (DefaultUniList a) = PIRTypeList (Just (defUniToType a))
defUniToType (DefaultUniPair a b) = PIRTypePair (Just $ defUniToType a) (Just $ defUniToType b)
defUniToType DefaultUniProtoList = PIRTypeList Nothing
defUniToType DefaultUniProtoPair = PIRTypePair Nothing Nothing
defUniToType (DefaultUniApply DefaultUniProtoPair a) = PIRTypePair (Just $ defUniToType a) Nothing
defUniToType x = error $ "defUniToType impossible: " ++ show x

-- | Untyped Plutus Constants
data PIRConstant
  = PIRConstInteger Integer
  | PIRConstByteString BS.ByteString
  | PIRConstUnit
  | PIRConstBool Bool
  | PIRConstString T.Text
  | PIRConstList [PIRConstant]
  | PIRConstPair PIRConstant PIRConstant
  | PIRConstData P.Data
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

defUniToConstant :: DefaultUni (P.Esc a) -> a -> PIRConstant
defUniToConstant DefaultUniInteger x = PIRConstInteger x
defUniToConstant DefaultUniByteString x = PIRConstByteString x
defUniToConstant DefaultUniUnit _ = PIRConstUnit
defUniToConstant DefaultUniBool x = PIRConstBool x
defUniToConstant DefaultUniString x = PIRConstString x
defUniToConstant DefaultUniData x = PIRConstData x
defUniToConstant (DefaultUniList a) x = PIRConstList (map (defUniToConstant a) x)
defUniToConstant (DefaultUniPair a b) x = PIRConstPair (defUniToConstant a (fst x)) (defUniToConstant b (snd x))
defUniToConstant uni _ = error $ "defUniToConstant impossible: " ++ show uni

instance Pretty PIRBuiltinType where
  pretty PIRTypeInteger = "Integer"
  pretty PIRTypeByteString = "ByteString"
  pretty PIRTypeUnit = "Unit"
  pretty PIRTypeBool = "Bool"
  pretty PIRTypeString = "String"
  pretty PIRTypeData = "Data"
  pretty (PIRTypeList a) = brackets (sep ["List", pretty a])
  pretty (PIRTypePair a b) = brackets (sep ["Pair", pretty a, pretty b])

instance Pretty (Maybe PIRBuiltinType) where
  pretty Nothing = "-"
  pretty (Just t) = pretty t

instance Pretty PIRConstant where
  pretty (PIRConstInteger x) = pretty x
  pretty (PIRConstByteString x) = "b" <> pretty x
  pretty PIRConstUnit = "unit"
  pretty (PIRConstBool x) = pretty x
  pretty (PIRConstString x) = dquotes (pretty x)
  pretty (PIRConstData d) = "d" <> braces (pretty d)
  pretty (PIRConstList xs) = "l" <> brackets (sep $ punctuate comma $ map pretty xs)
  pretty (PIRConstPair x y) = "p" <> brackets (sep $ punctuate comma $ map pretty [x, y])

instance Pretty P.Data where
  pretty (P.Constr cN fields) = pretty cN <+> pretty fields
  pretty (P.Map kvs) = pretty kvs
  pretty (P.List xs) = pretty xs
  pretty (P.I i) = pretty i
  pretty (P.B bs) = pretty bs
