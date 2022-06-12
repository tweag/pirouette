{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module declares 'PlutusIR' as a supported language, instantiates all the
--  necessary bits for using the facilities from "Pirouette.Term.Syntax" and provides
--  a translation function 'trProgram' to translate a plutusIR program into a 'PrtTerm'
--  and a map of definitions.
module Language.Pirouette.PlutusIR.Builtins where

import qualified Data.ByteString as BS
import Data.Data
import Data.String (fromString)
import qualified Data.Text as T
import Language.Haskell.TH.Syntax (Lift)
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import PlutusCore
  ( DefaultUni (..),
    pattern DefaultUniList,
    pattern DefaultUniPair,
    pattern DefaultUniString,
  )
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

deriving instance Lift P.Data

instance LanguageBuiltins BuiltinsOfPIR where
  type BuiltinTypes BuiltinsOfPIR = PIRBuiltinType
  type BuiltinTerms BuiltinsOfPIR = P.DefaultFun
  type Constants BuiltinsOfPIR = PIRConstant

cstToBuiltinType :: PIRConstant -> PIRBuiltinType
cstToBuiltinType (PIRConstInteger _) = PIRTypeInteger
cstToBuiltinType (PIRConstByteString _) = PIRTypeByteString
cstToBuiltinType PIRConstUnit = PIRTypeUnit
cstToBuiltinType (PIRConstBool _) = PIRTypeBool
cstToBuiltinType (PIRConstString _) = PIRTypeString
cstToBuiltinType (PIRConstList []) = PIRTypeList Nothing
cstToBuiltinType (PIRConstList (c : cs)) =
  let res = PIRTypeList (Just $ cstToBuiltinType c)
   in if all (== res) (cstToBuiltinType <$> cs)
        then res
        else error "typeOfConstant: mismatching element types in a PIRConstList"
cstToBuiltinType (PIRConstPair c1 c2) =
  PIRTypePair (Just (cstToBuiltinType c1)) (Just (cstToBuiltinType c2))
cstToBuiltinType (PIRConstData _) = PIRTypeData

-- | Shortcut for system F arrows
infixr 2 :->:

pattern (:->:) :: Type BuiltinsOfPIR -> Type BuiltinsOfPIR -> Type BuiltinsOfPIR
pattern (:->:) x y = SystF.TyFun x y

-- | Helper to lift PIR builtin types to system F
systfType :: PIRBuiltinType -> Type BuiltinsOfPIR
systfType = SystF.TyPure . SystF.Free . TyBuiltin

-- Shortcuts for PIR builtin types in systemF
tInt, tBool, tUnit, tByteString, tString, tData :: Type BuiltinsOfPIR
tInt = systfType PIRTypeInteger
tBool = systfType PIRTypeBool
tUnit = systfType PIRTypeUnit
tByteString = systfType PIRTypeByteString
tString = systfType PIRTypeString
tData = systfType PIRTypeData

-- | Shortcuts for type variables
tVar :: String -> Integer -> Type BuiltinsOfPIR
tVar name deBruijn = SystF.TyPure $ SystF.Bound (SystF.Ann (fromString name)) deBruijn

-- | Polymorphic PIR list type shortcut
tList :: Type BuiltinsOfPIR -> Type BuiltinsOfPIR
tList x = SystF.TyApp (SystF.Free (TyBuiltin (PIRTypeList Nothing))) [x]

-- | Polymorphic PIR pair type shortcut
tPair :: Type BuiltinsOfPIR -> Type BuiltinsOfPIR -> Type BuiltinsOfPIR
tPair x y = SystF.TyApp (SystF.Free (TyBuiltin (PIRTypePair Nothing Nothing))) [x, y]

-- | "Forall" type shortcut helper for types of kind *
forall :: SystF.Ann (SystF.Ann ann) -> SystF.AnnType ann tyVar -> SystF.AnnType ann tyVar
forall x = SystF.TyAll (SystF.ann x) SystF.KStar

instance LanguageBuiltinTypes BuiltinsOfPIR where
  typeOfConstant = systfType . cstToBuiltinType

  typeOfBuiltin P.AddInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.DivideInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.EqualsInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.LessThanInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.LessThanEqualsInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.EqualsByteString = tByteString :->: tByteString :->: tBool
  typeOfBuiltin P.IfThenElse = forall "a" (tBool :->: tVar "a" 0 :->: tVar "a" 0 :->: tVar "a" 0)
  typeOfBuiltin P.Trace = forall "a" (tString :->: tVar "a" 0 :->: tVar "a" 0)
  typeOfBuiltin P.FstPair = forall "a" (forall "b" (tPair (tVar "a" 1) (tVar "b" 0) :->: tVar "a" 1))
  typeOfBuiltin P.SndPair = forall "a" (forall "b" (tPair (tVar "a" 1) (tVar "b" 0) :->: tVar "b" 0))
  -- https://github.com/input-output-hk/plutus/blob/3c4067bb96251444c43ad2b17bc19f337c8b47d7/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs#L1009
  typeOfBuiltin P.ChooseList =
    forall "a" (forall "b" (tList (tVar "a" 1) :->: tVar "b" 0 :->: tVar "b" 0 :->: tVar "b" 0))
  typeOfBuiltin P.HeadList = forall "a" (tList (tVar "a" 0) :->: tVar "a" 0)
  typeOfBuiltin P.TailList = forall "a" (tList (tVar "a" 0) :->: tList (tVar "a" 0))
  -- https://github.com/input-output-hk/plutus/blob/3c4067bb96251444c43ad2b17bc19f337c8b47d7/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs#L1075
  typeOfBuiltin P.ChooseData =
    forall "a" (tData :->: tVar "a" 0 :->: tVar "a" 0 :->: tVar "a" 0 :->: tVar "a" 0 :->: tVar "a" 0 :->: tVar "a" 0)
  typeOfBuiltin P.UnConstrData = tData :->: tPair tInt (tList tData)
  typeOfBuiltin P.UnIData = tData :->: tInt
  typeOfBuiltin P.UnBData = tData :->: tByteString
  typeOfBuiltin P.MkNilData = tData
  -- TODO: implement the types of other builtins, but make sure to always bring in a golden
  -- test that comes from the plutus compiler. We should REALLY not be guessing these types,
  -- no matter how simple they seem.
  typeOfBuiltin builtin = error $ "typeOfBuiltin " ++ show builtin ++ " is not implemented"

  -- The type of bottom in PlutusIR is similar to Haskell; we translate @PIR.Error loc ty@
  -- to @Free Bottom `App` [TyArg ty]@.
  typeOfBottom = forall "a" (tVar "a" 0)

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
  deriving (Eq, Ord, Show, Read, Data, Typeable, Lift)

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
