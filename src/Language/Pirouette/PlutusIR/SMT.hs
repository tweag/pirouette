module Language.Pirouette.PlutusIR.SMT where

import qualified Data.Text as Text
import Language.Pirouette.PlutusIR.Builtins
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
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
-- TODO: Have an actual represention of data
trPIRType PIRTypeData = SimpleSMT.tUnit
trPIRType (PIRTypePair (Just pirType1) (Just pirType2)) =
  SimpleSMT.tTuple [trPIRType pirType1, trPIRType pirType2]
trPIRType pirType =
  error $ "Translate builtin type to smtlib: " <> show pirType <> " not yet handled."

-- TODO Implement remaining constants
trPIRConstant :: PIRConstant -> SimpleSMT.SExpr
trPIRConstant (PIRConstInteger n) = SimpleSMT.int n
trPIRConstant (PIRConstByteString bs) = error "Not implemented: PIRConstByteString to SMT"
trPIRConstant PIRConstUnit = SimpleSMT.unit
trPIRConstant (PIRConstBool b) = SimpleSMT.bool b
trPIRConstant (PIRConstString txt) = SimpleSMT.string (Text.unpack txt)
trPIRConstant (PIRConstList l) = error "Not implemented: PIRConstList to SMT"
trPIRConstant (PIRConstPair x y) = error "Not implemented: PIRConstPair to SMT"
trPIRConstant (PIRConstData dat) = error "Not implemented: PIRConstData to SMT"

trPIRFun :: P.DefaultFun -> [SimpleSMT.SExpr] -> Maybe SimpleSMT.SExpr

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
    P.Trace -> Just $ SimpleSMT.List [x]
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
    P.AddInteger -> Just $ SimpleSMT.add x y
    P.SubtractInteger -> Just $ SimpleSMT.sub x y
    P.MultiplyInteger -> Just $ SimpleSMT.mul x y
    P.DivideInteger -> Just $ SimpleSMT.div x y
    P.ModInteger -> Just $ SimpleSMT.mod x y
    P.EqualsInteger -> Just $ SimpleSMT.eq x y
    P.LessThanInteger -> Just $ SimpleSMT.lt x y
    P.LessThanEqualsInteger -> Just $ SimpleSMT.leq x y
    P.EqualsByteString -> Just $ SimpleSMT.eq x y
    P.EqualsString -> Just $ SimpleSMT.eq x y
    P.EqualsData -> Just $ SimpleSMT.eq x y
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
