{-# LANGUAGE QuasiQuotes #-}
-- -l has the effect of causing the TH interpreter to try loading
-- z3 to resolve otherwise undefined symbols
{-# OPTIONS_GHC -lz3 #-}

module Language.Pirouette.Example.IsUnity where

import Language.Pirouette.Example
import Language.Pirouette.Example.StdLib (progWithStdLib)
import Pirouette.Monad
import Pirouette.Symbolic.Prover.Runner
import qualified Test.Tasty.HUnit as Test

checkWrong :: Test.Assertion
checkWrong =
  assertIncorrectnessLogic
    15
    definitions
    IncorrectnessParams
      { ipTarget = [term| \(tx : TxInfo) . validator tx |], -- validator
        ipTargetType = [ty| Bool |],
        ipCondition =
          [term| \(result : Bool) (tx : TxInfo) . result |] -- incorrectness triple
            :==>: [term| \(result : Bool) (tx : TxInfo) . correct_validator tx |]
      }

checkOk :: Test.Assertion
checkOk =
  assertIncorrectnessLogic
    20
    definitions
    IncorrectnessParams
      { ipTarget = [term| \(tx : TxInfo) . correct_validator tx |], -- validator
        ipTargetType = [ty| Bool |],
        ipCondition =
          [term| \(result : Bool) (tx : TxInfo) . result |] -- incorrectness triple
            :==>: [term| \(result : Bool) (tx : TxInfo) . correct_validator tx |]
      }

definitions :: PrtUnorderedDefs Ex
definitions =
  [progWithStdLib|
eqInt : Integer -> Integer -> Bool
eqInt x y = x == y

eqString : String -> String -> Bool
eqString x y = x ~~ y

data Pair x y
  = P : x -> y -> Pair x y

pairEq :
  forall a b .
  (a -> a -> Bool) ->
  (b -> b -> Bool) ->
  Pair a b -> Pair a b -> Bool
pairEq @a @b eqA eqB x y =
  match_Pair @a @b x @Bool
    (\(x0 : a) (x1 : b) . match_Pair @a @b y @Bool
      (\(y0 : a) (y1 : b) . and (eqA x0 y0) (eqB x1 y1)))

data KVMap k v
  = KV : List (Pair k v) -> KVMap k v

toList : forall k v . KVMap k v -> List (Pair k v)
toList @k @v m = match_KVMap @k @v m @(List (Pair k v)) (\(x : List (Pair k v)) . x)

lkupOne : forall k v . (k -> Bool) -> Pair k v -> Maybe v
lkupOne @k @v predi m =
  match_Pair @k @v m @(Maybe v)
    (\(fst : k) (snd : v) . if @(Maybe v) predi fst then Just @v snd else Nothing @v)

lkup : forall k v . (k -> k -> Bool) -> KVMap k v -> k -> Maybe v
lkup @k @v eq m tgt =
  match_KVMap @k @v m @(Maybe v)
    (foldr @(Pair k v) @(Maybe v) (\(pk : Pair k v) . firstJust @v (lkupOne @k @v (eq tgt) pk)) (Nothing @v))

-- Just like a plutus value, but se use integers for currency symbols and token names
-- to not have to deal with bytestrings
data Value
  = V : KVMap String (KVMap String Integer) -> Value

-- Definitions of Plutus transactions
data Address
  = A : Integer -> Address
data TxOut
  = MkTxOut : Address -> Value -> TxOut
data TxId
  = Id : Integer -> TxId
data TxOutRef
  = MkTxOutRef : TxId -> Integer -> TxOutRef
data TxInfo
  = MkTxInfo : List (Pair TxOutRef TxOut) -> List TxOut -> Value -> Value -> TxId -> TxInfo

-- Analogous to Plutus assetClassValueOf
assetClassValueOf : Value -> Pair String String -> Integer
assetClassValueOf v ac =
  match_Pair @String @String ac @Integer
    (\(curSym : String) (tokName : String) .
      match_Value v @Integer
        (\(openV : KVMap String (KVMap String Integer)) .
          match_Maybe @(KVMap String Integer) (lkup @String @(KVMap String Integer) eqString openV curSym) @Integer
            0
            (\(tokM : KVMap String Integer) .
              match_Maybe @Integer (lkup @String @Integer eqString tokM tokName) @Integer
                0
                (\(r : Integer) . r))))

-- Now we define the wrong isUnity function, that is too permissive
wrong_isUnity : Value -> Pair String String -> Bool
wrong_isUnity v ac = assetClassValueOf v ac == 1

-- The correct spec for that should be exactly what we wrote in our blogpost:
--
-- > isUnity :: Value -> AssetClass -> Bool
-- > isUnity v c = Map.lookup curr (getValue v) == Just (Map.fromList [(tok, 1)])
-- >  where (curr, tok) = unAssetClass c
--
-- In our example language, that gets a little more verbose! :P
correct_isUnity : Value -> Pair String String -> Bool
correct_isUnity v ac =
  match_Pair @String @String ac @Bool
    (\(curSym : String) (tokName : String) .
      match_Value v @Bool
        (\(openV : KVMap String (KVMap String Integer)) .
          match_Maybe @(KVMap String Integer) (lkup @String @(KVMap String Integer) eqString openV curSym) @Bool
            False
            (\(tokM : KVMap String Integer) .
              eqList @(Pair String Integer)
                (pairEq @String @Integer eqString eqInt)
                (toList @String @Integer tokM)
                (Cons @(Pair String Integer) (P @String @Integer tokName 1) (Nil @(Pair String Integer))))))

-- Now we define a simple example asset class
example_ac : Pair String String
example_ac = P @String @String "currency" "token"

eqTxOutRef : TxOutRef -> TxOutRef -> Bool
eqTxOutRef r1 r2 =
  match_TxOutRef r1 @Bool
    (\(i1 : TxId) (ix1 : Integer)
    . match_TxOutRef r2 @Bool
        (\(i2 : TxId) (ix2 : Integer)
        . match_TxId i1 @Bool
            (\(n1 : Integer)
            . match_TxId i2 @Bool
              (\(n2 : Integer)
              . and (eqInt n1 n2) (eqInt ix1 ix2)
              ))))

spendsOutput : List (Pair TxOutRef TxOut) -> TxOutRef -> Bool
spendsOutput inputs wanted =
    any @(Pair TxOutRef TxOut)
      (\(p : Pair TxOutRef TxOut)
      . match_Pair @TxOutRef @TxOut p @Bool (\(r : TxOutRef) (o : TxOut) . eqTxOutRef wanted r))
      inputs

example_out : TxOutRef
example_out = MkTxOutRef (Id 42) 0

-- And the infamous validator, slightly simplified:
validator : TxInfo -> Bool
validator tx =
    match_TxInfo tx @Bool
    (\(inputs : List (Pair TxOutRef TxOut)) (outputs : List TxOut) (fee : Value) (mint : Value) (txId : TxId).
      and (spendsOutput inputs example_out) (wrong_isUnity mint example_ac))

-- And the infamous validator, slightly simplified:
correct_validator : TxInfo -> Bool
correct_validator tx =
    match_TxInfo tx @Bool
    (\(inputs : List (Pair TxOutRef TxOut)) (outputs : List TxOut) (fee : Value) (mint : Value) (txId : TxId).
      correct_isUnity mint example_ac)
|]
