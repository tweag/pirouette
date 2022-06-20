{-# LANGUAGE OverloadedStrings #-}

module Language.Pirouette.PlutusIR.SMT where

import Data.Text (Text)
import Language.Pirouette.PlutusIR.Syntax
import Pirouette.Monad
import Pirouette.Symbolic.Eval.Types
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF as SystemF
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
trPIRFun P.UnConstrData _ = Nothing
trPIRFun P.UnMapData _ = Nothing
trPIRFun P.UnListData _ = Nothing
trPIRFun P.UnIData _ = Nothing
trPIRFun P.UnBData _ = Nothing
-- If-then-else is complicated
trPIRFun P.IfThenElse _ = Nothing

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
    -- and these are for Data
    P.MapData -> Just $ PureSMT.fun "Map" [x]
    P.ListData -> Just $ PureSMT.fun "List" [x]
    P.IData -> Just $ PureSMT.fun "I" [x]
    P.BData -> Just $ PureSMT.fun "B" [x]
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
    P.MkPairData -> Just $ PureSMT.fun "Tuple2" [x, y]
    P.ConstrData -> Just $ PureSMT.fun "Constr" [x, y]
    _ ->
      error $
        "Translate builtin to SMT: "
          <> show op
          <> " is not an implemented binary operator/function"

-- Remainder
trPIRFun op _ =
  error $
    "Translate builtin to SMT: "
      <> show op
      <> " is not an implemented constant/operator/function"

instance LanguageSymEval PlutusIR where
  -- applying constructors functions during evaluation
  -- is quite useful because we tend can interact with
  -- the pattern matching much better b/c we know
  -- the constructor that has been applied

  branchesBuiltinTerm P.MkNilData _ _args =
    continueWith "Nil" []
  branchesBuiltinTerm P.MkNilPairData _ _args =
    continueWith "Nil" []
  branchesBuiltinTerm P.MkCons _ _args =
    continueWith "Nil" []

  branchesBuiltinTerm P.ConstrData _ args =
    continueWith "Constr" args
  branchesBuiltinTerm P.MapData _ args =
    continueWith "Map" args
  branchesBuiltinTerm P.ListData _ args =
    continueWith "List" args
  branchesBuiltinTerm P.IData _ args =
    continueWith "I" args
  branchesBuiltinTerm P.BData _ args =
    continueWith "B" args

  -- pattern matching and built-in matchers

  branchesBuiltinTerm P.ChooseList _ args = 
    continueWith "Nil_match" args
  branchesBuiltinTerm P.ChooseUnit _ args = 
    continueWith "Unit_match" args
  branchesBuiltinTerm P.ChooseData _ args = 
    continueWith "Data_match" args

  branchesBuiltinTerm P.FstPair _ [tyA@(TyArg a), tyB@(TyArg b), tuple] =
    continueWith "Tuple2_match"
      [ tyA, tyB, tuple, tyA
      , TermArg $ Lam (Ann "x") a $ Lam (Ann "y") b $ App (Bound (Ann "x") 1) [] ]
  branchesBuiltinTerm P.SndPair _ [tyA@(TyArg a), tyB@(TyArg b), tuple] =
    continueWith "Tuple2_match"
      [ tyA, tyB, tuple, tyB
      , TermArg $ Lam (Ann "x") a $ Lam (Ann "y") b $ App (Bound (Ann "y") 0) [] ]

  branchesBuiltinTerm P.HeadList _ [tyA@(TyArg a), lst] =
    continueWith "List_match"
      [ tyA, lst, tyA
      , TermArg errorTerm
      , TermArg $ Lam (Ann "x") a $ Lam (Ann "xs") (listOf a) $ App (Bound (Ann "x") 1) [] ]
  branchesBuiltinTerm P.TailList _ [tyA@(TyArg a), lst] =
    continueWith "List_match"
      [ tyA, lst, TyArg (listOf a)
      , TermArg errorTerm
      , TermArg $ Lam (Ann "x") a $ Lam (Ann "xs") (listOf a) $ App (Bound (Ann "xs") 0) [] ]

  branchesBuiltinTerm P.NullList _ [tyA@(TyArg a), lst] =
    continueWith "List_match"
      [ tyA, lst, TyArg (builtin PIRTypeBool)
      , TermArg $ App (Free $ TermSig "True") []
      , TermArg $ Lam (Ann "x") a $ Lam (Ann "xs") (listOf a) $ App (Free $ TermSig "False") [] ]

  branchesBuiltinTerm P.UnConstrData _ [d] =
    continueWith "Data_match"
      [ d, TyArg (builtin (PIRTypePair (Just PIRTypeInteger) (Just PIRTypeData)))
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) 
                $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) 
                $ App (Free $ TermSig "Tuple2") [TermArg $ App (Bound (Ann "i") 1) [], TermArg $ App (Bound (Ann "ds") 0) []]
      , TermArg $ Lam (Ann "es") (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) errorTerm
      , TermArg $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) errorTerm
      , TermArg $ Lam (Ann "b") (builtin PIRTypeByteString) errorTerm ]
  branchesBuiltinTerm P.UnMapData _ [d] =
    continueWith "Data_match"
      [ d, TyArg (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData))))
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger)  $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "es") (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) $ App (Bound (Ann "es") 0) []
      , TermArg $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) errorTerm
      , TermArg $ Lam (Ann "b") (builtin PIRTypeByteString) errorTerm ]
  branchesBuiltinTerm P.UnListData _ [d] =
    continueWith "Data_match"
      [ d, TyArg (listOf (builtin PIRTypeData))
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger)  $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "es") (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) $ App (Bound (Ann "es") 0) []
      , TermArg $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) errorTerm
      , TermArg $ Lam (Ann "b") (builtin PIRTypeByteString) errorTerm ]
  branchesBuiltinTerm P.UnIData _ [d] =
    continueWith "Data_match"
      [ d, TyArg (builtin PIRTypeInteger)
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger)  $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "es") (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) errorTerm
      , TermArg $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) $ App (Bound (Ann "es") 0) []
      , TermArg $ Lam (Ann "b") (builtin PIRTypeByteString) errorTerm ]
  branchesBuiltinTerm P.UnBData _ [d] =
    continueWith "Data_match"
      [ d, TyArg (builtin PIRTypeByteString)
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger)  $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "es") (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) errorTerm
      , TermArg $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) errorTerm
      , TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) errorTerm
      , TermArg $ Lam (Ann "b") (builtin PIRTypeByteString) $ App (Bound (Ann "es") 0) [] ]

  branchesBuiltinTerm _rest _translator _args = 
    pure Nothing

continueWith :: 
  (ToSMT meta, PirouetteReadDefs lang m) =>
  Text -> [ArgMeta lang meta] ->
  m (Maybe [Branch lang meta])
continueWith destr args = do
  destr' <- contextualizeTermName destr
  pure $ Just [ Branch { additionalInfo = mempty, newTerm = App (Free $ TermSig destr') args }]

errorTerm :: AnnTerm ty ann (SystemF.VarMeta meta ann (TermBase lang))
errorTerm = App (Free Bottom) []

listOf :: AnnType ann (SystemF.VarMeta meta ann (TypeBase lang)) -> AnnType ann (SystemF.VarMeta meta ann (TypeBase lang))
listOf x = TyApp (Free $ TySig "List") [x]

builtin :: PIRBuiltinType -> AnnType ann (SystemF.VarMeta meta ann (TypeBase PlutusIR))
builtin nm = TyApp (Free $ TyBuiltin nm) []