module Language.Pirouette.PlutusIR.SMT where

import qualified Data.Text as Text
import Language.Pirouette.PlutusIR.Syntax
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
import qualified PlutusCore as P
import qualified PureSMT

instance LanguageSMT PlutusIR where
  translateBuiltinType = trPIRType

  -- translateBuiltinTerm = error "translateBuiltinTerm (t :: BuiltinTerms PlutusIR): not yet impl"
  translateBuiltinTerm = trPIRFun
  translateConstant = trPIRConstant
  isStuckBuiltin = error "isStuckBuiltin (t :: TermMeta PlutusIR meta): not yet impl"

instance LanguageSMTBranches PlutusIR where
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

-- TODO Implement remaining constants
trPIRConstant :: PIRConstant -> PureSMT.SExpr
trPIRConstant (PIRConstInteger n) = PureSMT.int n
trPIRConstant (PIRConstByteString bs) = error "Not implemented: PIRConstByteString to SMT"
trPIRConstant PIRConstUnit = PureSMT.unit
trPIRConstant (PIRConstBool b) = PureSMT.bool b
trPIRConstant (PIRConstString txt) = PureSMT.string (Text.unpack txt)
trPIRConstant (PIRConstList l) = error "Not implemented: PIRConstList to SMT"
trPIRConstant (PIRConstPair x y) = error "Not implemented: PIRConstPair to SMT"
trPIRConstant (PIRConstData dat) = error "Not implemented: PIRConstData to SMT"

trPIRFun :: P.DefaultFun -> [PureSMT.SExpr] -> Maybe PureSMT.SExpr

-- TODO Implement remaining builtins: those used by the "Auction" example
-- validator are marked with an [A] and as commented out lines in the
-- code afterwards

-- ** Integers **

--
--     P.QuotientInteger
--     P.RemainderInteger
--

-- ** Bytestrings **

--
--     P.AppendByteString
--     P.ConsByteString
--     P.SliceByteString
--     P.LengthOfByteString
--     P.IndexByteString
--     P.EqualsByteString
--     P.LessThanByteString
--     P.LessThanEqualsByteString
--

-- ** Hash and signatures **

--
--     P.Sha2_256
--     P.Sha3_256
--     P.Blake2b_256
--     P.VerifySignature
--

-- ** Strings and encoding **

--
--     P.AppendString
--     P.EqualsString
--     P.EncodeUtf8
--     P.DecodeUtf8
--

-- ** If then else **

--
-- [A] P.IfThenElse
--

-- ** Lists and pairs **

--
-- [A] P.FstPair
-- [A] P.SndPair
-- [A] P.ChooseList
--     P.MkCons
-- [A] P.HeadList
-- [A] P.TailList
--     P.NullList

-- ** Data **

--
--     P.ChooseUnit
-- [A] P.ChooseData
--     P.ConstrData
--     P.MapData
--     P.ListData
--     P.IData
--     P.BData
-- [A] P.UnConstrData
--     P.UnMapData
--     P.UnListData
-- [A] P.UnIData
-- [A] P.UnBData
--     P.MkPairData
--     P.MkNilData
--     P.MkNilPairData

-- Unary
trPIRFun op [x] =
  case op of
    P.Trace -> Just $ PureSMT.List [x]
    -- P.FstPair ->
    -- P.SndPair ->
    -- P.HeadList ->
    -- P.TailList ->
    -- P.UnConstrData ->
    -- P.UnIData ->
    -- P.UnBData ->
    _ ->
      error $
        "Translate builtin to SMT: "
          <> show op
          <> " is not an implemented unary operator/function"
-- Binary
trPIRFun op [x, y] =
  case op of
    P.AddInteger -> Just $ PureSMT.add x y
    P.SubtractInteger -> Just $ PureSMT.sub x y
    P.MultiplyInteger -> Just $ PureSMT.mul x y
    P.DivideInteger -> Just $ PureSMT.div x y
    P.ModInteger -> Just $ PureSMT.mod x y
    P.EqualsInteger -> Just $ PureSMT.eq x y
    P.LessThanInteger -> Just $ PureSMT.lt x y
    P.LessThanEqualsInteger -> Just $ PureSMT.leq x y
    P.EqualsByteString -> Just $ PureSMT.eq x y
    P.EqualsString -> Just $ PureSMT.eq x y
    P.EqualsData -> Just $ PureSMT.eq x y
    _ ->
      error $
        "Translate builtin to SMT: "
          <> show op
          <> " is not an implemented binary operator/function"
-- Ternary
trPIRFun op [x, y, z] =
{-
  case op of
    -- P.IfThenElse ->
    -- P.ChooseList ->
    _ ->
-}
      error $
        "Translate builtin to SMT: "
          <> show op
          <> " is not an implemented ternary operator/function"
-- Remainder
trPIRFun op _ =
{-
  case op of
    -- P.ChooseData ->
    _ ->
-}
      error $
        "Translate builtin to SMT: "
          <> show op
          <> " is not an implemented constant/operator/function"
