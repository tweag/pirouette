{-# LANGUAGE OverloadedStrings #-}

module Language.Pirouette.PlutusIR.SMT where

import Data.Text (Text)
import Language.Pirouette.PlutusIR.Syntax
import Pirouette.Monad
import Pirouette.Symbolic.Eval.Types
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF
import Pirouette.Transformations.Contextualize (contextualizeTermName)
import qualified PlutusCore as P
import qualified PureSMT

-- See https://github.com/input-output-hk/plutus/blob/master/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs

instance LanguageSMT PlutusIR where
  translateBuiltinType = trPIRType

  -- translateBuiltinTerm = error "translateBuiltinTerm (t :: BuiltinTerms PlutusIR): not yet impl"
  translateBuiltinTerm = trPIRFun
  translateConstant = trPIRConstant

  isStuckBuiltin e
    | termIsConstant e = True
    | Just _ <- termIsMeta e = True
  isStuckBuiltin (App (Free (Builtin op)) args)
    | op `elem` plutusIRBasicOps || op `elem` plutusIRBasicRels
    = let args' = map (\(TermArg a) -> a) args
      in all isStuckBuiltin args' && not (all termIsConstant args')
  isStuckBuiltin _ = False

  builtinTypeDefinitions =
    [ -- list, pair, and unit are defined whenever they are needed
      -- in the PIR files themselves
      {- ("list", listTypeDef), ("unit", unitTypeDef), -}
      ("Data", dataTypeDef)]
    where
      base nm = TyApp (Free $ TySig nm) []
      builtin :: PIRBuiltinType -> Type PlutusIR
      builtin nm = TyApp (Free $ TyBuiltin nm) []
      listOf x = TyApp (Free $ TySig "List") [x]

      {-
      a = TyApp (Bound (Ann "a") 0) []

      listTypeDef = Datatype {
        kind = KTo KStar KStar
      , typeVariables = [("a", KStar)]
      , destructor = "list_match"
      , constructors = [
          ("Nil", TyAll (Ann "a") KStar (listOf a))
        , ("Cons", TyAll (Ann "a") KStar (TyFun a (TyFun (listOf a) (listOf a))))
        ]
      }

      unitTypeDef = Datatype {
        kind = KStar
      , typeVariables = []
      , destructor = "unit_match"
      , constructors = [("Unit", base "unit")]
      }
      -}

      -- defined following https://github.com/input-output-hk/plutus/blob/master/plutus-core/plutus-core/src/PlutusCore/Data.hs
      dataTypeDef = Datatype {
        kind = KStar
      , typeVariables = []
      , destructor = "Data_match"
      , constructors = [
          ("Constr", TyFun (builtin PIRTypeInteger) (TyFun (listOf (base "data")) (base "data")))
        , ("Map", TyFun (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) (base "data"))
        , ("List", TyFun (listOf (base "data")) (base "data"))
        , ("I", TyFun (builtin PIRTypeInteger) (base "data"))
        , ("B", TyFun (builtin PIRTypeByteString) (base "data"))
        ]
      }

trPIRType :: PIRBuiltinType -> PureSMT.SExpr
trPIRType PIRTypeInteger = PureSMT.tInt
trPIRType PIRTypeBool = PureSMT.tBool
trPIRType PIRTypeString = PureSMT.tString
trPIRType PIRTypeByteString = PureSMT.tString
trPIRType PIRTypeUnit = PureSMT.fun "Unit" []
trPIRType PIRTypeData = PureSMT.tUnit -- TODO: Temporary represention of data
-- Note: why do Pair have maybes?
-- Note answer, because types can be partially applied in System F,
-- and `Pair a` is represented by `PIRTypePair (pirType a) Nothing`
trPIRType (PIRTypePair (Just pirType1) (Just pirType2)) =
  PureSMT.fun "Tuple2" [trPIRType pirType1, trPIRType pirType2]
trPIRType (PIRTypeList (Just pirType)) =
  PureSMT.fun "List" [trPIRType pirType]
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
trPIRConstant (PIRConstPair x y) = PureSMT.fun "Tuple2" [trPIRConstant x, trPIRConstant y]
trPIRConstant (PIRConstData _dat) = error "Not implemented: PIRConstData to SMT"

plutusIRBasicOps :: [P.DefaultFun]
plutusIRBasicOps = [
  P.AddInteger, P.SubtractInteger, P.MultiplyInteger,
  P.DivideInteger, P.ModInteger, P.QuotientInteger, P.RemainderInteger,
  P.AppendString ]

plutusIRBasicRels :: [P.DefaultFun]
plutusIRBasicRels = [
  P.EqualsInteger, P.LessThanInteger, P.LessThanEqualsInteger,
  P.EqualsByteString, P.EqualsString, P.EqualsData ]

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
-- Pattern matching in disguise,
-- so we return here Nothing and then "translate"
-- into an actual match in 'branchesBuiltinTerm'
trPIRFun P.ChooseList _ = Nothing
trPIRFun P.ChooseUnit _ = Nothing
trPIRFun P.ChooseData _ = Nothing
trPIRFun P.FstPair _ = Nothing
trPIRFun P.SndPair _ = Nothing
trPIRFun P.HeadList _ = Nothing
trPIRFun P.TailList _ = Nothing
-- If-then-else is complicated
trPIRFun P.IfThenElse _ = Nothing
-- Remainder
trPIRFun op _ =
  error $
    "Translate builtin to SMT: "
      <> show op
      <> " is not an implemented constant/operator/function"

instance LanguageSymEval PlutusIR where
  branchesBuiltinTerm P.ChooseList _translator args = 
    continueWithMatch "Nil_match" args
  branchesBuiltinTerm P.ChooseUnit _translator args = 
    continueWithMatch "Unit_match" args
  branchesBuiltinTerm P.ChooseData _translator args = 
    continueWithMatch "Data_match" args

  branchesBuiltinTerm _rest _translator _args = 
    pure Nothing

continueWithMatch :: 
  (ToSMT meta, PirouetteReadDefs lang m) =>
  Text -> [ArgMeta lang meta] ->
  m (Maybe [Branch lang meta])
continueWithMatch destr args = do
  destr' <- contextualizeTermName destr
  pure $ Just [ Branch { additionalInfo = mempty, newTerm = App (Free $ TermSig destr') args }]