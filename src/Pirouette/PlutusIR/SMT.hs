module Pirouette.PlutusIR.SMT where

import Pirouette.Term.Syntax.Base
import Pirouette.SMT.Common
import Pirouette.PlutusIR.ToTerm
import qualified Pirouette.SMT.SimpleSMT as SmtLib

instance LanguageSMT PlutusIR where
  translateBuiltinType = trPIRType
  translateBuiltinTerm = _
  translateConstant = _

trPIRType :: PIRType -> SmtLib.SExpr
trPIRType PIRTypeInteger = SmtLib.tInt
trPIRType PIRTypeBool = SmtLib.tBool
trPIRType PIRTypeString = SmtLib.tString
trPIRType PIRTypeByteString = SmtLib.tString
trPIRType PIRTypeUnit = SmtLib.tUnit
trPIRType PIRTypeData = SmtLib.tUnit -- TODO: Temporary represention of data
-- Note: why do Pair have maybes?
-- Note answer, because types can be partially applied in System F,
-- and `Pair a` is represented by `PIRTypePair (pirType a) Nothing`
trPIRType (PIRTypePair (Just pirType1) (Just pirType2)) =
  SmtLib.tTuple [trPIRType pirType1, trPIRType pirType2]
trPIRType pirType =
  error $ "Translate builtin type to smtlib: " <> show pirType <> " not yet handled."
