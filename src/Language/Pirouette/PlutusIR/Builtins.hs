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

infixr 2 :->:

pattern (:->:) :: SystF.AnnType ann tyVar -> SystF.AnnType ann tyVar -> SystF.AnnType ann tyVar
pattern (:->:) x y = SystF.TyFun x y

systfType :: PIRBuiltinType -> TypeMeta BuiltinsOfPIR meta
systfType = SystF.TyPure . SystF.Free . TyBuiltin

tInt, tBool, tUnit, tByteString, tString, tData :: TypeMeta BuiltinsOfPIR meta
tInt = systfType PIRTypeInteger
tBool = systfType PIRTypeBool
tUnit = systfType PIRTypeUnit
tByteString = systfType PIRTypeByteString
tString = systfType PIRTypeString
tData = systfType PIRTypeData

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

-- | Shortcuts for type variables
a, b :: TypeMeta BuiltinsOfPIR meta
a = SystF.TyPure $ SystF.Bound (SystF.Ann "a") 0
b = SystF.TyPure $ SystF.Bound (SystF.Ann "b") 0

-- | Polymorphic PIR list type shortcut
tList :: TypeMeta BuiltinsOfPIR meta -> TypeMeta BuiltinsOfPIR meta
tList x = SystF.TyApp (SystF.Free (TyBuiltin (PIRTypeList Nothing))) [x]

-- | Polymorphic PIR pair type shortcut
tPair :: TypeMeta BuiltinsOfPIR meta -> TypeMeta BuiltinsOfPIR meta -> TypeMeta BuiltinsOfPIR meta
tPair x y = SystF.TyApp (SystF.Free (TyBuiltin (PIRTypePair Nothing Nothing))) [x, y]

-- | "Forall" type shortcut helper for types of kind *
forall :: SystF.Ann (SystF.Ann ann) -> SystF.AnnType ann tyVar -> SystF.AnnType ann tyVar
forall x = SystF.TyAll (SystF.ann x) SystF.KStar

instance LanguageBuiltinTypes BuiltinsOfPIR where
  typeOfConstant = systfType . cstToBuiltinType
  typeOfBuiltin P.AddInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.SubtractInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.MultiplyInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.DivideInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.QuotientInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.RemainderInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.ModInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.EqualsInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.LessThanInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.LessThanEqualsInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.AppendByteString = tByteString :->: tByteString :->: tByteString
  typeOfBuiltin P.ConsByteString = undefined
  typeOfBuiltin P.SliceByteString = undefined
  typeOfBuiltin P.LengthOfByteString = tByteString :->: tInt
  typeOfBuiltin P.IndexByteString = undefined
  typeOfBuiltin P.EqualsByteString = tByteString :->: tByteString :->: tBool
  typeOfBuiltin P.LessThanByteString = tByteString :->: tByteString :->: tBool
  typeOfBuiltin P.LessThanEqualsByteString = tByteString :->: tByteString :->: tBool
  typeOfBuiltin P.Sha2_256 = undefined
  typeOfBuiltin P.Sha3_256 = undefined
  typeOfBuiltin P.Blake2b_256 = undefined
  typeOfBuiltin P.VerifySignature = undefined
  typeOfBuiltin P.AppendString = tString :->: tString :->: tString
  typeOfBuiltin P.EqualsString = tString :->: tString :->: tBool
  typeOfBuiltin P.EncodeUtf8 = undefined
  typeOfBuiltin P.DecodeUtf8 = undefined
  typeOfBuiltin P.IfThenElse = forall "a" (tBool :->: a :->: a)
  typeOfBuiltin P.ChooseUnit = undefined
  typeOfBuiltin P.Trace = forall "a" (tString :->: a :->: a)
  typeOfBuiltin P.FstPair = forall "a" (forall "b" (tPair a b :->: a))
  typeOfBuiltin P.SndPair = forall "a" (forall "b" (tPair a b :->: b))
  typeOfBuiltin P.ChooseList = forall "a" (tList a :->: forall "b" (b :->: (a :->: tList a :->: b))) -- REQUIRED BY "AUCTION"
  typeOfBuiltin P.MkCons = forall "a" (a :->: tList a :->: a)
  typeOfBuiltin P.HeadList = forall "a" (tList a :->: a) -- REQUIRED BY "AUCTION"
  typeOfBuiltin P.TailList = forall "a" (tList a :->: tList a) -- REQUIRED BY "AUCTION"
  typeOfBuiltin P.NullList = forall "a" (tList a)
  typeOfBuiltin P.ChooseData = -- REQUIRED BY "AUCTION"
    forall "a"
    (
    -- fConstr
    -- Should we use PIRTypeList (Just PIRTypeData) or apply a polymorphic PIRTypeList to tData?
    (tInt :->: systfType (PIRTypeList (Just PIRTypeData)) :->: a)
    :->: 
    -- fMap
    -- Same question for list + same question for pair
    (systfType (PIRTypeList (Just (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) :->: a)
    :->: 
    -- fList
    -- Same question for list
    (systfType (PIRTypeList (Just PIRTypeData)) :->: a)
    :->: 
    -- fI
    (tInt :->: a)
    :->: 
    -- fB
    (tByteString :->: a)
    )
  typeOfBuiltin P.ConstrData = undefined
  typeOfBuiltin P.MapData = undefined
  typeOfBuiltin P.ListData = undefined
  typeOfBuiltin P.IData = undefined
  typeOfBuiltin P.BData = undefined
  typeOfBuiltin P.UnConstrData = undefined -- TODO REQUIRED BY "AUCTION"
  typeOfBuiltin P.UnMapData = undefined
  typeOfBuiltin P.UnListData = -- REQUIRED BY "AUCTION"
    -- Should we use PIRTypeList (Just PIRTypeData) or apply a polymorphic PIRTypeList to tData?
    tData :->: systfType (PIRTypeList (Just PIRTypeData))
  typeOfBuiltin P.UnIData = tData :->: tInt -- REQUIRED BY "AUCTION"
  typeOfBuiltin P.UnBData = tData :->: tByteString -- REQUIRED BY "AUCTION"
  typeOfBuiltin P.EqualsData = tData :->: tData :->: tBool
  typeOfBuiltin P.MkPairData = tData :->: tData :->: systfType (PIRTypePair (Just PIRTypeData) (Just PIRTypeData))
  typeOfBuiltin P.MkNilData = tData
  typeOfBuiltin P.MkNilPairData = undefined
  typeOfBottom = error "No bottom type in PIR"

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
