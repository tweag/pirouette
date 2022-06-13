module Language.Pirouette.PlutusIR.SMT where

import Language.Pirouette.PlutusIR.Builtins
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
import qualified PureSMT

instance LanguageSMT BuiltinsOfPIR where
  translateBuiltinType = trPIRType
  translateBuiltinTerm = error "translateBuiltinTerm (t :: BuiltinTerms PlutusIR): not yet impl"
  translateConstant = error "translateConstant (t :: Constants PlutusIR): not yet impl"
  isStuckBuiltin = error "isStuckBuiltin (t :: TermMeta PlutusIR meta): not yet impl"

instance LanguageSMTBranches BuiltinsOfPIR where
  branchesBuiltinTerm _tm _translator _args = pure Nothing

trPIRType :: PIRBuiltinType -> PureSMT.SExpr
trPIRType PIRTypeInteger = PureSMT.tInt
trPIRType PIRTypeBool = PureSMT.tBool
trPIRType PIRTypeString = PureSMT.tString
trPIRType PIRTypeByteString = PureSMT.tString
trPIRType PIRTypeUnit = PureSMT.tUnit
trPIRType PIRTypeData = PureSMT.tUnit -- TODO: Temporary represention of data
-- Note: why do Pair have maybes?
-- Note answer, because types can be partially applied in System F,
-- and `Pair a` is represented by `PIRTypePair (pirType a) Nothing`
trPIRType (PIRTypePair (Just pirType1) (Just pirType2)) =
  PureSMT.tTuple [trPIRType pirType1, trPIRType pirType2]
trPIRType pirType =
  error $ "Translate builtin type to smtlib: " <> show pirType <> " not yet handled."
