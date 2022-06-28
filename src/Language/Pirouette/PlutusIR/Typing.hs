{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Defines the 'LanguageBuiltinTypes' instance for 'PlutusIR',
-- the only export of this module is that instance.
module Language.Pirouette.PlutusIR.Typing () where

import Data.String (fromString)
import Language.Pirouette.PlutusIR.Syntax
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import qualified PlutusCore as P

-- | Shortcut for system F arrows
infixr 2 :->:

pattern (:->:) :: Type PlutusIR -> Type PlutusIR -> Type PlutusIR
pattern (:->:) x y = SystF.TyFun x y

-- | Helper to lift PIR builtin types to system F
systfType :: PIRBuiltinType -> Type PlutusIR
systfType = SystF.TyPure . SystF.Free . TyBuiltin

-- Shortcuts for PIR builtin types in systemF
tInt, tBool, _tUnit, tByteString, tString, tData :: Type PlutusIR
tInt = systfType PIRTypeInteger
tBool = systfType PIRTypeBool
_tUnit = systfType PIRTypeUnit
tByteString = systfType PIRTypeByteString
tString = systfType PIRTypeString
tData = systfType PIRTypeData

-- | Shortcuts for type variables
tVar :: String -> Integer -> Type PlutusIR
tVar name deBruijn = SystF.TyPure $ SystF.Bound (SystF.Ann (fromString name)) deBruijn

-- | Polymorphic PIR list type shortcut
tList :: Type PlutusIR -> Type PlutusIR
tList x = SystF.TyApp (SystF.Free (TyBuiltin (PIRTypeList Nothing))) [x]

-- | Polymorphic PIR pair type shortcut
tPair :: Type PlutusIR -> Type PlutusIR -> Type PlutusIR
tPair x y = SystF.TyApp (SystF.Free (TyBuiltin (PIRTypePair Nothing Nothing))) [x, y]

-- | "Forall" type shortcut helper for types of kind *
forall :: SystF.Ann (SystF.Ann ann) -> SystF.AnnType ann tyVar -> SystF.AnnType ann tyVar
forall x = SystF.TyAll (SystF.ann x) SystF.KStar

instance LanguageBuiltinTypes PlutusIR where
  typeOfConstant = systfType . cstToBuiltinType

  typeOfBuiltin P.AddInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.SubtractInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.MultiplyInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.DivideInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.ModInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.QuotientInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.RemainderInteger = tInt :->: tInt :->: tInt
  typeOfBuiltin P.EqualsInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.LessThanInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.LessThanEqualsInteger = tInt :->: tInt :->: tBool
  typeOfBuiltin P.EqualsString = tString :->: tString :->: tBool
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
