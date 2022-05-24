module Language.Pirouette.PlutusIR.SMT where

import Language.Pirouette.PlutusIR.Builtins
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
import qualified Data.Text as Text
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import qualified PlutusCore as P

instance LanguageSMT BuiltinsOfPIR where
  translateBuiltinType = trPIRType
  -- translateBuiltinTerm = error "translateBuiltinTerm (t :: BuiltinTerms PlutusIR): not yet impl"
  translateBuiltinTerm = trPIRFun
  translateConstant = trPIRConstant
  isStuckBuiltin = error "isStuckBuiltin (t :: TermMeta PlutusIR meta): not yet impl"

instance LanguageSMTBranches BuiltinsOfPIR where
  branchesBuiltinTerm _tm _translator _args = pure Nothing

trPIRType :: PIRBuiltinType -> SimpleSMT.SExpr
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

trPIRConstant :: PIRConstant -> SimpleSMT.SExpr
trPIRConstant (PIRConstInteger n) = SimpleSMT.int n
trPIRConstant (PIRConstByteString bs) = error "Not implemented: PIRConstByteString to SMT"
trPIRConstant PIRConstUnit = SimpleSMT.unit
trPIRConstant (PIRConstBool b) = SimpleSMT.bool b
trPIRConstant (PIRConstString txt) = SimpleSMT.string (Text.unpack txt)
trPIRConstant (PIRConstList pcs) = error "Not implemented: PIRConstList to SMT"
trPIRConstant (PIRConstPair pc1 pc2) = error "Not implemented: PIRConstPair to SMT"
trPIRConstant (PIRConstData dat) = error "Not implemented: PIRConstData to SMT"

trPIRFun :: P.DefaultFun -> [SimpleSMT.SExpr] -> Maybe SimpleSMT.SExpr
-- Integers
trPIRFun P.AddInteger [x, y] = Just $ SimpleSMT.add x y
trPIRFun P.AddInteger _ = error "PIR AddInteger to SMT: not applied to 2 args"
trPIRFun P.SubtractInteger [x, y] = Just $ SimpleSMT.sub x y
trPIRFun P.SubtractInteger _ = error "PIR SubInteger to SMT: not applied to 2 args"
trPIRFun P.MultiplyInteger [x, y] = Just $ SimpleSMT.mul x y
trPIRFun P.MultiplyInteger _ = error "PIR MultiplyInteger to SMT: not applied to 2 args"
trPIRFun P.DivideInteger [x, y] = Just $ SimpleSMT.div x y
trPIRFun P.DivideInteger _ = error "PIR DivideInteger to SMT: not applied to 2 args"
trPIRFun P.QuotientInteger _ = error "Not implemented: PIR builtin function" -- TODO Implement in SimpleSMT
trPIRFun P.RemainderInteger _ = error "Not implemented: PIR builtin function" -- TODO Implement in SimpleSMT
trPIRFun P.ModInteger [x, y] = Just $ SimpleSMT.mul x y
trPIRFun P.ModInteger _ = error "PIR ModInteger to SMT: not applied to 2 args"
trPIRFun P.EqualsInteger [x, y] = Just $ SimpleSMT.eq x y
trPIRFun P.EqualsInteger _ = error "PIR EqualsInteger to SMT: not applied to 2 args"
trPIRFun P.LessThanInteger [x, y] = Just $ SimpleSMT.lt x y
trPIRFun P.LessThanInteger _ = error "PIR LessThanInteger to SMT: not applied to 2 args"
trPIRFun P.LessThanEqualsInteger [x, y] = Just $ SimpleSMT.leq x y
trPIRFun P.LessThanEqualsInteger _ = error "PIR LessThanEqualsInteger to SMT: not applied to 2 args"
-- Bytestrings
trPIRFun P.AppendByteString _ = error "Not implemented: PIR builtin function"
trPIRFun P.ConsByteString _ = error "Not implemented: PIR builtin function"
trPIRFun P.SliceByteString _ = error "Not implemented: PIR builtin function"
trPIRFun P.LengthOfByteString _ = error "Not implemented: PIR builtin function"
trPIRFun P.IndexByteString _ = error "Not implemented: PIR builtin function"
trPIRFun P.EqualsByteString [x, y] = Just $ SimpleSMT.eq x y
trPIRFun P.EqualsByteString _ = error "PIR EqualsByteString to SMT: not applied to 2 args"
trPIRFun P.LessThanByteString _ = error "Not implemented: PIR builtin function"
trPIRFun P.LessThanEqualsByteString _ = error "Not implemented: PIR builtin function"
-- Hash and signatures
trPIRFun P.Sha2_256 _ = error "Not implemented: PIR builtin function"
trPIRFun P.Sha3_256 _ = error "Not implemented: PIR builtin function"
trPIRFun P.Blake2b_256 _ = error "Not implemented: PIR builtin function"
trPIRFun P.VerifySignature _ = error "Not implemented: PIR builtin function"
-- Strings and encoding
trPIRFun P.AppendString _ = error "Not implemented: PIR builtin function"
trPIRFun P.EqualsString [x, y] = Just $ SimpleSMT.eq x y
trPIRFun P.EqualsString _ = error "PIR EqualsString to SMT: not applied to 2 args"
trPIRFun P.EncodeUtf8 _ = error "Not implemented: PIR builtin function"
trPIRFun P.DecodeUtf8 _ = error "Not implemented: PIR builtin function"
-- If then else
trPIRFun P.IfThenElse _ = error "Not implemented: PIR builtin function"
trPIRFun P.ChooseUnit _ = error "Not implemented: PIR builtin function"
-- Lists and pairs
trPIRFun P.Trace _ = error "Not implemented: PIR builtin function"
trPIRFun P.FstPair _ = error "Not implemented: PIR builtin function"
trPIRFun P.SndPair _ = error "Not implemented: PIR builtin function"
trPIRFun P.ChooseList _ = error "Not implemented: PIR builtin function"
trPIRFun P.MkCons _ = error "Not implemented: PIR builtin function"
trPIRFun P.HeadList _ = error "Not implemented: PIR builtin function"
trPIRFun P.TailList _ = error "Not implemented: PIR builtin function"
trPIRFun P.NullList _ = error "Not implemented: PIR builtin function"
-- Data
trPIRFun P.ChooseData _ = error "Not implemented: PIR builtin function"
trPIRFun P.ConstrData _ = error "Not implemented: PIR builtin function"
trPIRFun P.MapData _ = error "Not implemented: PIR builtin function"
trPIRFun P.ListData _ = error "Not implemented: PIR builtin function"
trPIRFun P.IData _ = error "Not implemented: PIR builtin function"
trPIRFun P.BData _ = error "Not implemented: PIR builtin function"
trPIRFun P.UnConstrData _ = error "Not implemented: PIR builtin function"
trPIRFun P.UnMapData _ = error "Not implemented: PIR builtin function"
trPIRFun P.UnListData _ = error "Not implemented: PIR builtin function"
trPIRFun P.UnIData _ = error "Not implemented: PIR builtin function"
trPIRFun P.UnBData _ = error "Not implemented: PIR builtin function"
trPIRFun P.EqualsData [x, y] = Just $ SimpleSMT.eq x y
trPIRFun P.EqualsData _ = error "PIR EqualsData to SMT: not applied to 2 args"
trPIRFun P.MkPairData _ = error "Not implemented: PIR builtin function"
trPIRFun P.MkNilData _ = error "Not implemented: PIR builtin function"
trPIRFun P.MkNilPairData _ = error "Not implemented: PIR builtin function"
