module Pirouette.PlutusIR.SMT where

import Pirouette.Term.Syntax.Base
import Pirouette.SMT.Base
import Pirouette.PlutusIR.ToTerm
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT

instance LanguageSMT PlutusIR where
  translateBuiltinType = trPIRType
  translateBuiltinTerm = error "translateBuiltinTerm (t :: BuiltinTerms PlutusIR): not yet impl"
  translateConstant = error "translateConstant (t :: Constants PlutusIR): not yet impl"

trPIRType :: PIRType -> SimpleSMT.SExpr
trPIRType PIRTypeInteger = SimpleSMT.tInt
trPIRType PIRTypeBool = SimpleSMT.tBool
trPIRType PIRTypeString = SimpleSMT.tString
trPIRType PIRTypeByteString = SimpleSMT.tString
trPIRType PIRTypeUnit = SimpleSMT.tUnit
trPIRType PIRTypeData = SimpleSMT.tUnit -- TODO: Temporary represention of data
-- Note: why do Pair have maybes?
-- Note answer, because types can be partially applied in System F,
-- and `Pair a` is represented by `PIRTypePair (pirType a) Nothing`
trPIRType (PIRTypePair (Just pirType1) (Just pirType2)) =
  SimpleSMT.tTuple [trPIRType pirType1, trPIRType pirType2]
trPIRType pirType =
  error $ "Translate builtin type to smtlib: " <> show pirType <> " not yet handled."
