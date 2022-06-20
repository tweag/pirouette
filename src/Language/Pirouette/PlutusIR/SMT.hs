{-# LANGUAGE OverloadedStrings #-}

module Language.Pirouette.PlutusIR.SMT where

import Language.Pirouette.PlutusIR.Syntax
import Pirouette.Monad
import Pirouette.Symbolic.Eval.Types
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF
import qualified PlutusCore as P
import qualified PureSMT

-- See https://github.com/input-output-hk/plutus/blob/master/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs

instance LanguageSMT PlutusIR where
  translateBuiltinType = trPIRType

  -- translateBuiltinTerm = error "translateBuiltinTerm (t :: BuiltinTerms PlutusIR): not yet impl"
  translateBuiltinTerm = trPIRFun
  translateConstant = trPIRConstant
  isStuckBuiltin = error "isStuckBuiltin (t :: TermMeta PlutusIR meta): not yet impl"

  builtinTypeDefinitions =
    [("list", listTypeDef), ("unit", unitTypeDef)]
    where
      listTypeDef = Datatype {
        kind = KTo KStar KStar
      , typeVariables = [("a", KStar)]
      , destructor = "list_match"
      , constructors = [
          ("Nil", TyAll (Ann "a") KStar listOfA)
        , ("Cons", TyAll (Ann "a") KStar (TyFun variableA (TyFun listOfA listOfA)))
        ]
      }
      variableA = TyApp (Bound (Ann "a") 0) []
      listOfA = TyApp (Free $ TySig "list") [variableA]

      unitTypeDef = Datatype {
        kind = KStar
      , typeVariables = []
      , destructor = "unit_match"
      , constructors = [("Unit", TyApp (Free $ TySig "unit") [])]
      }

trPIRType :: PIRBuiltinType -> PureSMT.SExpr
trPIRType PIRTypeInteger = PureSMT.tInt
trPIRType PIRTypeBool = PureSMT.tBool
trPIRType PIRTypeString = PureSMT.tString
trPIRType PIRTypeByteString = PureSMT.tString
trPIRType PIRTypeUnit = PureSMT.fun "unit" []
trPIRType PIRTypeData = PureSMT.tUnit -- TODO: Temporary represention of data
-- Note: why do Pair have maybes?
-- Note answer, because types can be partially applied in System F,
-- and `Pair a` is represented by `PIRTypePair (pirType a) Nothing`
trPIRType (PIRTypePair (Just pirType1) (Just pirType2)) =
  PureSMT.tTuple [trPIRType pirType1, trPIRType pirType2]
trPIRType (PIRTypeList (Just pirType)) =
  PureSMT.fun "list" [trPIRType pirType]
trPIRType pirType =
  error $ "Translate builtin type to smtlib: " <> show pirType <> " not yet handled."

-- TODO Implement remaining constants
trPIRConstant :: PIRConstant -> PureSMT.SExpr
trPIRConstant (PIRConstInteger n) = PureSMT.int n
trPIRConstant (PIRConstByteString _bs) = error "Not implemented: PIRConstByteString to SMT"
trPIRConstant PIRConstUnit = PureSMT.fun "Unit" []
trPIRConstant (PIRConstBool b) = PureSMT.bool b
trPIRConstant (PIRConstString txt) = PureSMT.text txt
trPIRConstant (PIRConstList lst) = go lst 
  where go [] = PureSMT.fun "Nil" []
        go (x:xs) = PureSMT.fun "Cons" [trPIRConstant x, go xs]
trPIRConstant (PIRConstPair x y) = PureSMT.tuple [trPIRConstant x, trPIRConstant y]
trPIRConstant (PIRConstData _dat) = error "Not implemented: PIRConstData to SMT"

trPIRFun :: P.DefaultFun -> [PureSMT.SExpr] -> Maybe PureSMT.SExpr

-- TODO Implement remaining builtins: those used by the "Auction" example
-- validator are marked with an [A] and as commented out lines in the
-- code afterwards

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
--     P.EncodeUtf8
--     P.DecodeUtf8
--

-- ** Data **

--
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

-- Unary
trPIRFun op [x] =
  case op of
    P.Trace -> Just $ PureSMT.List [x]
    -- some simple operations
    P.NullList -> Just $ PureSMT.eq x (PureSMT.fun "Nil" [])
    P.FstPair -> Just $ PureSMT.tupleSel 0 x
    P.SndPair -> Just $ PureSMT.tupleSel 1 x
    -- constructors
    -- those are defined as unary functions for historical reasons
    P.MkNilData -> Just $ PureSMT.fun "Nil" []
    P.MkNilPairData -> Just $ PureSMT.fun "Nil" []
    _ ->
      error $
        "Translate builtin to SMT: "
          <> show op
          <> " is not an implemented unary operator/function"
-- Binary operations and relations
trPIRFun op [x, y] =
  case op of
    -- integer operations
    P.AddInteger -> Just $ PureSMT.add x y
    P.SubtractInteger -> Just $ PureSMT.sub x y
    P.MultiplyInteger -> Just $ PureSMT.mul x y
    -- divMod and quotRem work differently
    -- when not exact, but this is a good approximation
    P.DivideInteger -> Just $ PureSMT.div x y
    P.ModInteger -> Just $ PureSMT.mod x y
    P.QuotientInteger -> Just $ PureSMT.div x y
    P.RemainderInteger -> Just $ PureSMT.mod x y
    -- operations over other types
    P.AppendString -> Just $ PureSMT.fun "str.++" [x, y]
    -- relations
    P.EqualsInteger -> Just $ PureSMT.eq x y
    P.LessThanInteger -> Just $ PureSMT.lt x y
    P.LessThanEqualsInteger -> Just $ PureSMT.leq x y
    P.EqualsByteString -> Just $ PureSMT.eq x y
    P.EqualsString -> Just $ PureSMT.eq x y
    P.EqualsData -> Just $ PureSMT.eq x y
    -- constructors
    P.MkCons -> Just $ PureSMT.fun "Cons" [x, y]
    P.MkPairData -> Just $ PureSMT.tuple [x, y]
    _ ->
      error $
        "Translate builtin to SMT: "
          <> show op
          <> " is not an implemented binary operator/function"
-- Pattern matching in disguise
trPIRFun P.IfThenElse _ = Nothing
trPIRFun P.ChooseList _ = Nothing
trPIRFun P.HeadList _ = Nothing
trPIRFun P.TailList _ = Nothing
trPIRFun P.ChooseUnit _ = Nothing
trPIRFun P.ChooseData _ = Nothing
-- Remainder
trPIRFun op _ =
  error $
    "Translate builtin to SMT: "
      <> show op
      <> " is not an implemented constant/operator/function"

instance LanguageSymEval PlutusIR where
  branchesBuiltinTerm P.ChooseList _translator args = 
    continueWithMatch "list_match" args
  branchesBuiltinTerm P.ChooseUnit _translator args = 
    continueWithMatch "unit_match" args
  branchesBuiltinTerm P.ChooseData _translator args = 
    continueWithMatch "data_match" args

  branchesBuiltinTerm _rest _translator _args = 
    pure Nothing

continueWithMatch :: 
  (ToSMT meta, PirouetteReadDefs lang m) =>
  Name -> [ArgMeta lang meta] ->
  m (Maybe [Branch lang meta])
continueWithMatch destr args =
  pure $ Just [ Branch { additionalInfo = mempty, newTerm = App (Free $ TermSig destr) args }]