{-# LANGUAGE QuasiQuotes #-}

module Language.Pirouette.Example.IsUnity where

import Language.Pirouette.Example
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
  [prog|
and :
  Bool ->
  Bool ->
  Bool
and x y = if @Bool x then y else False

or : Bool -> Bool -> Bool
or x y = if @Bool x then True else y

eqInt : Integer -> Integer -> Bool
eqInt x y = x == y

eqString : String -> String -> Bool
eqString x y = x ~~ y

data List a
  = Nil : List a
  | Cons : a -> List a -> List a

foldr : forall a r . (a -> r -> r) -> r -> List a -> r
foldr @a @r f e l =
  match_List @a l @r
    e
    (\(x : a) (xs : List a) . f x (foldr @a @r f e xs))

listEq :
  forall a .
  (a -> a -> Bool) ->
  List a -> List a -> Bool
listEq @a eq x0 y0 =
  match_List @a x0 @Bool
    (match_List @a y0 @Bool True (\(y : a) (ys : List a) . False))
    (\(x : a) (xs : List a) .
      match_List @a y0 @Bool False (\(y : a) (ys : List a) . and (eq x y) (listEq @a eq xs ys)))

contains : forall a . (a -> Bool) -> List a -> Bool
contains @a eq x0 =
  match_List @a x0 @Bool
    False
    (\(x : a) (xs : List a) . or (eq x) (contains @a eq xs))

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

data Maybe x
  = Just : x -> Maybe x
  | Nothing : Maybe x

maybeSum : forall x . Maybe x -> Maybe x -> Maybe x
maybeSum @x mx my =
  match_Maybe @x mx @(Maybe x)
    (\(jx : x) . Just @x jx)
    my

isJust : forall x . Maybe x -> Bool
isJust @x mx =
  match_Maybe @x mx @Bool (\(jx : x) . True) False

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
    (foldr @(Pair k v) @(Maybe v) (\(pk : Pair k v) . maybeSum @v (lkupOne @k @v (eq tgt) pk)) (Nothing @v))

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
    (\(curSym : String) (tokName : String)
     . match_Value v @Integer
     (\(openV : KVMap String (KVMap String Integer))
      . match_Maybe @(KVMap String Integer) (lkup @String @(KVMap String Integer) eqString openV curSym) @Integer
          (\(tokM : KVMap String Integer)
           . match_Maybe @Integer (lkup @String @Integer eqString tokM tokName) @Integer
               (\(r : Integer) . r)
               0
          )
          0
    ))

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
    (\(curSym : String) (tokName : String)
     . match_Value v @Bool
     (\(openV : KVMap String (KVMap String Integer))
      . match_Maybe @(KVMap String Integer) (lkup @String @(KVMap String Integer) eqString openV curSym) @Bool
          (\(tokM : KVMap String Integer)
           . listEq @(Pair String Integer)
               (pairEq @String @Integer eqString eqInt)
               (toList @String @Integer tokM)
               (Cons @(Pair String Integer) (P @String @Integer tokName 1) (Nil @(Pair String Integer))))
          False
     ))

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
    contains @(Pair TxOutRef TxOut)
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
