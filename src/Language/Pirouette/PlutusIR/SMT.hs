{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.Pirouette.PlutusIR.SMT where

import qualified Data.ByteString as BS
import Data.Text (Text)
import Language.Pirouette.PlutusIR.Syntax
import Pirouette.Monad
import Pirouette.SMT.Base
import Pirouette.SMT.Constraints
import Pirouette.Symbolic.Eval.BranchingHelpers
import Pirouette.Symbolic.Eval.Types
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF as SystemF
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
    | op `elem` plutusIRBasicOps || op `elem` plutusIRBasicRels,
      all isArg args -- this ensures that we only have TermArg
      =
      let args' = map (\(TermArg a) -> a) args
       in all isStuckBuiltin args' && not (all termIsConstant args')
  isStuckBuiltin _ = False

trPIRType :: PIRBuiltinType -> PureSMT.SExpr
trPIRType PIRTypeInteger = PureSMT.tInt
trPIRType PIRTypeBool = PureSMT.tBool
trPIRType PIRTypeString = PureSMT.tString
trPIRType PIRTypeByteString = PureSMT.tString
trPIRType PIRTypeUnit = PureSMT.fun "pir_Unit" []
trPIRType PIRTypeData = PureSMT.fun "pir_Data" []
-- Note: why do Pair have maybes?
-- Note answer, because types can be partially applied in System F,
-- and `Pair a` is represented by `PIRTypePair (pirType a) Nothing`
trPIRType (PIRTypePair (Just pirType1) (Just pirType2)) =
  PureSMT.fun "pir_Tuple2" [trPIRType pirType1, trPIRType pirType2]
trPIRType (PIRTypeList (Just pirType)) =
  PureSMT.fun "pir_List" [trPIRType pirType]
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
  where
    go [] = PureSMT.fun "Nil" []
    go (x : xs) = PureSMT.fun "Cons" [trPIRConstant x, go xs]
trPIRConstant (PIRConstPair x y) = PureSMT.fun "Tuple2" [trPIRConstant x, trPIRConstant y]
trPIRConstant (PIRConstData _dat) = error "Not implemented: PIRConstData to SMT"

-- | These operations can be fully evaluated
-- if the given arguments are constants.
-- For example, @3 + 4@ is *not* stuck.
plutusIRBasicOps :: [P.DefaultFun]
plutusIRBasicOps =
  [ P.AddInteger,
    P.SubtractInteger,
    P.MultiplyInteger,
    P.DivideInteger,
    P.ModInteger,
    P.QuotientInteger,
    P.RemainderInteger,
    P.AppendString,
    P.AppendByteString,
    P.ConsByteString,
    P.IndexByteString,
    P.SliceByteString
  ]

-- | These relations can be fully evaluated
-- if the given arguments are constants.
-- For example, @3 < 4@ is *not* stuck.
plutusIRBasicRels :: [P.DefaultFun]
plutusIRBasicRels =
  [ P.EqualsInteger,
    P.LessThanInteger,
    P.LessThanEqualsInteger,
    P.EqualsByteString,
    P.EqualsString,
    P.EqualsData,
    P.LessThanByteString,
    P.LessThanEqualsByteString
  ]

trPIRFun :: P.DefaultFun -> [PureSMT.SExpr] -> Maybe PureSMT.SExpr

-- TODO Implement remaining builtins: those used by the "Auction" example
-- validator are marked with an [A] and as commented out lines in the
-- code afterwards

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

pattern K :: Constants lang -> AnnTerm ty ann (SystemF.VarMeta meta ann (TermBase lang))
pattern K n = App (Free (Constant n)) []

instance LanguageSymEval PlutusIR where
  -- basic operations over constants

  branchesBuiltinTerm op _ [TermArg (K (PIRConstInteger x)), TermArg (K (PIRConstInteger y))]
    | op `elem` plutusIRBasicOps || op `elem` plutusIRBasicRels =
      (\r -> pure $ Just [Branch {additionalInfo = mempty, newTerm = K r}]) $
        case op of
          P.AddInteger -> PIRConstInteger $ x + y
          P.SubtractInteger -> PIRConstInteger $ x - y
          P.MultiplyInteger -> PIRConstInteger $ x * y
          P.DivideInteger -> PIRConstInteger $ x `div` y
          P.ModInteger -> PIRConstInteger $ x `mod` y
          P.QuotientInteger -> PIRConstInteger $ x `quot` y
          P.RemainderInteger -> PIRConstInteger $ x `rem` y
          P.EqualsInteger -> PIRConstBool $ x == y
          P.LessThanInteger -> PIRConstBool $ x < y
          P.LessThanEqualsInteger -> PIRConstBool $ x <= y
          _ -> error "ill-typed application"
  branchesBuiltinTerm op _ [TermArg (K (PIRConstByteString x)), TermArg (K (PIRConstByteString y))]
    | op `elem` plutusIRBasicOps || op `elem` plutusIRBasicRels =
      (\r -> pure $ Just [Branch {additionalInfo = mempty, newTerm = K r}]) $
        case op of
          P.AppendByteString -> PIRConstByteString (x <> y)
          P.EqualsByteString -> PIRConstBool $ x == y
          P.LessThanByteString -> PIRConstBool $ x < y
          P.LessThanEqualsByteString -> PIRConstBool $ x <= y
          _ -> error "ill-typed application"
  branchesBuiltinTerm P.LengthOfByteString _ [TermArg (K (PIRConstByteString b))] =
    let r = K $ PIRConstInteger (fromIntegral $ BS.length b)
     in pure $ Just [Branch {additionalInfo = mempty, newTerm = r}]
  branchesBuiltinTerm
    P.ConsByteString
    _
    [TermArg (K (PIRConstInteger i)), TermArg (K (PIRConstByteString b))] =
      let r = K $ PIRConstByteString (BS.cons (fromInteger i) b)
       in pure $ Just [Branch {additionalInfo = mempty, newTerm = r}]
  branchesBuiltinTerm
    P.IndexByteString
    _
    [TermArg (K (PIRConstByteString b)), TermArg (K (PIRConstInteger i))] =
      let r =
            if i < 0
              then errorTerm
              else K $ PIRConstInteger $ fromIntegral (BS.index b (fromInteger i))
       in pure $ Just [Branch {additionalInfo = mempty, newTerm = r}]
  branchesBuiltinTerm
    P.IndexByteString
    _
    [TermArg (K (PIRConstInteger start)), TermArg (K (PIRConstInteger n)), TermArg (K (PIRConstByteString xs))] =
      let r = K $ PIRConstByteString $ BS.take (fromInteger n) (BS.drop (fromInteger start) xs)
       in pure $ Just [Branch {additionalInfo = mempty, newTerm = r}]
  branchesBuiltinTerm op _ [TermArg (K (PIRConstString x)), TermArg (K (PIRConstString y))]
    | op `elem` plutusIRBasicOps || op `elem` plutusIRBasicRels =
      (\r -> pure $ Just [Branch {additionalInfo = mempty, newTerm = K r}]) $
        case op of
          P.AppendString -> PIRConstString $ x <> y
          P.EqualsString -> PIRConstBool $ x == y
          _ -> error "ill-typed application"
  branchesBuiltinTerm op _ [TermArg (K (PIRConstData x)), TermArg (K (PIRConstData y))]
    | op `elem` plutusIRBasicOps || op `elem` plutusIRBasicRels =
      (\r -> pure $ Just [Branch {additionalInfo = mempty, newTerm = K r}]) $
        case op of
          P.EqualsData -> PIRConstBool $ x == y
          _ -> error "ill-typed application"
  -- if-then-else goes to the helpers
  branchesBuiltinTerm P.IfThenElse _ (TyArg _ : TermArg c : TermArg t : TermArg e : excess) =
    let isEq P.EqualsInteger = True
        isEq P.EqualsString = True
        isEq P.EqualsByteString = True
        isEq P.EqualsData = True
        isEq _ = False
        isTrue (K (PIRConstBool True)) = True
        isTrue _ = False
        isFalse (K (PIRConstBool False)) = True
        isFalse _ = False
     in ifThenElseBranching
          isTrue
          (K (PIRConstBool True))
          isFalse
          (K (PIRConstBool False))
          isEq
          c
          t
          e
          excess
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
    continueWith "Data_Constr" args
  branchesBuiltinTerm P.MapData _ args =
    continueWith "Data_Map" args
  branchesBuiltinTerm P.ListData _ args =
    continueWith "Data_List" args
  branchesBuiltinTerm P.IData _ args =
    continueWith "Data_I" args
  branchesBuiltinTerm P.BData _ args =
    continueWith "Data_B" args
  -- pattern matching and built-in matchers

  -- they take the arguments in a different order
  branchesBuiltinTerm
    P.ChooseList
    _
    (TyArg a : TyArg tyR : TermArg lst : TermArg caseNil : TermArg caseCons : excess) =
      continueWithListMatch a tyR lst caseNil caseCons excess
  branchesBuiltinTerm P.ChooseUnit _ (tyR : unit : rest) =
    continueWith "Unit_match" (unit : tyR : rest)
  branchesBuiltinTerm
    P.ChooseData
    _
    (tyR : dat : TermArg caseC : TermArg caseM : TermArg caseL : TermArg caseI : TermArg caseB : excess) =
      continueWithDataMatch dat tyR caseC caseM caseL caseI caseB excess
  -- built-in matchers

  branchesBuiltinTerm P.FstPair _ [tyA@(TyArg a), tyB@(TyArg b), tuple] =
    continueWith
      "Tuple2_match"
      [ tyA,
        tyB,
        tuple,
        tyA,
        TermArg $ Lam (Ann "x") a $ Lam (Ann "y") b $ App (Bound (Ann "x") 1) []
      ]
  branchesBuiltinTerm P.SndPair _ [tyA@(TyArg a), tyB@(TyArg b), tuple] =
    continueWith
      "Tuple2_match"
      [ tyA,
        tyB,
        tuple,
        tyB,
        TermArg $ Lam (Ann "x") a $ Lam (Ann "y") b $ App (Bound (Ann "y") 0) []
      ]
  branchesBuiltinTerm P.HeadList _ [TyArg a, TermArg lst] =
    continueWithListMatch a a lst errorTerm (App (Bound (Ann "x") 1) []) []
  branchesBuiltinTerm P.TailList _ [TyArg a, TermArg lst] =
    continueWithListMatch a (listOf a) lst errorTerm (App (Bound (Ann "xs") 0) []) []
  branchesBuiltinTerm P.NullList _ [TyArg a, TermArg lst] =
    continueWithListMatch
      a
      (builtin PIRTypeBool)
      lst
      (K $ PIRConstBool True)
      (K $ PIRConstBool False)
      []
  branchesBuiltinTerm P.UnConstrData _ [d] =
    continueWithDataMatch
      d
      (TyArg (builtin (PIRTypePair (Just PIRTypeInteger) (Just PIRTypeData))))
      (App (Free $ TermSig "Tuple2") [TermArg $ App (Bound (Ann "i") 1) [], TermArg $ App (Bound (Ann "ds") 0) []])
      errorTerm
      errorTerm
      errorTerm
      errorTerm
      []
  branchesBuiltinTerm P.UnMapData _ [d] =
    continueWithDataMatch
      d
      (TyArg (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))))
      errorTerm
      (App (Bound (Ann "es") 0) [])
      errorTerm
      errorTerm
      errorTerm
      []
  branchesBuiltinTerm P.UnListData _ [d] =
    continueWithDataMatch
      d
      (TyArg (listOf (builtin PIRTypeData)))
      errorTerm
      errorTerm
      (App (Bound (Ann "ds") 0) [])
      errorTerm
      errorTerm
      []
  branchesBuiltinTerm P.UnIData _ [d] =
    continueWithDataMatch
      d
      (TyArg (builtin PIRTypeInteger))
      errorTerm
      errorTerm
      errorTerm
      (App (Bound (Ann "i") 0) [])
      errorTerm
      []
  branchesBuiltinTerm P.UnBData _ [d] =
    continueWithDataMatch
      d
      (TyArg (builtin PIRTypeByteString))
      errorTerm
      errorTerm
      errorTerm
      errorTerm
      (App (Bound (Ann "b") 0) [])
      []
  branchesBuiltinTerm _rest _translator _args =
    pure Nothing

-- | Indicates that the next step in the evaluation of that
-- built-in is the given function with the given arguments.
-- There's quite some boilerplate around it, hence this utility.
continueWith ::
  (ToSMT meta, Applicative m) =>
  Text ->
  [ArgMeta lang meta] ->
  m (Maybe [Branch lang meta])
continueWith destr args = do
  let destr' = Name destr Nothing
      tm = App (Free $ TermSig destr') args
  pure $ Just [Branch {additionalInfo = mempty, newTerm = tm}]

-- | Indicates that the next step is an application of
-- the List destructor. Note that this function does *not*
-- include any check for well-scopedness, so be careful!
continueWithListMatch ::
  (ToSMT meta, Applicative m, lang ~ PlutusIR) =>
  TypeMeta lang meta ->
  TypeMeta lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  [ArgMeta lang meta] ->
  m (Maybe [Branch lang meta])
continueWithListMatch tyA tyR lst caseNil caseCons excess =
  continueWith
    "Nil_match"
    [ TyArg tyA,
      TermArg lst,
      TyArg tyR,
      TermArg $ caseNil `appN` excess,
      TermArg $ Lam (Ann "x") tyA $ Lam (Ann "xs") (listOf tyA) $ caseCons `appN` excess
    ]

-- | Indicates that the next step is an application of
-- the Data destructor. Note that this function does *not*
-- include any check for well-scopedness, so be careful!
continueWithDataMatch ::
  (ToSMT meta, Applicative m, lang ~ PlutusIR) =>
  ArgMeta lang meta ->
  ArgMeta lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  [ArgMeta lang meta] ->
  m (Maybe [Branch lang meta])
continueWithDataMatch dat tyR caseC caseM caseL caseI caseB excess =
  continueWith
    "Data_match"
    [ dat,
      tyR,
      TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) caseC `appN` excess,
      TermArg $ Lam (Ann "es") (listOf (builtin (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) $ caseM `appN` excess,
      TermArg $ Lam (Ann "ds") (listOf (builtin PIRTypeData)) $ caseL `appN` excess,
      TermArg $ Lam (Ann "i") (builtin PIRTypeInteger) $ caseI `appN` excess,
      TermArg $ Lam (Ann "b") (builtin PIRTypeByteString) $ caseB `appN` excess
    ]

errorTerm :: AnnTerm ty ann (SystemF.VarMeta meta ann (TermBase lang))
errorTerm = App (Free Bottom) []

listOf ::
  AnnType ann (SystemF.VarMeta meta ann (TypeBase lang)) ->
  AnnType ann (SystemF.VarMeta meta ann (TypeBase lang))
listOf x = TyApp (Free $ TySig "List") [x]

tuple2Of ::
  AnnType ann (SystemF.VarMeta meta ann (TypeBase lang)) ->
  AnnType ann (SystemF.VarMeta meta ann (TypeBase lang)) ->
  AnnType ann (SystemF.VarMeta meta ann (TypeBase lang))
tuple2Of x y = TyApp (Free $ TySig "Tuple2") [x, y]

builtin :: PIRBuiltinType -> AnnType ann (SystemF.VarMeta meta ann (TypeBase PlutusIR))
builtin nm = TyApp (Free $ TyBuiltin nm) []
