{-# LANGUAGE QuasiQuotes #-}

module Language.Pirouette.Example.MinSwap where

import Language.Pirouette.Example.QuasiQuoter
import Language.Pirouette.Example.Syntax
import Pirouette.Term.Symbolic.Prover.Runner
import Pirouette.Term.Syntax.Base

checkWrong :: IO ()
checkWrong =
  incorrectnessLogic
    100 -- amount of steps
    minswap -- entire program
    [term| \(tx : TxInfo) . validator tx |] -- validator
    ( [term| \(result : Bool) (tx : TxInfo) . result |] -- incorrectness triple
        :==>: [term| \(result : Bool) (tx : TxInfo) . correct_validator tx |]
    )

checkOk :: IO ()
checkOk =
  incorrectnessLogic
    150 -- amount of steps
    minswap -- entire program
    [term| \(tx : TxInfo) . correct_validator tx |] -- validator
    ( [term| \(result : Bool) (tx : TxInfo) . result |] -- incorrectness triple
        :==>: [term| \(result : Bool) (tx : TxInfo) . correct_validator tx |]
    )

minswap :: Program Ex
minswap =
  [prog|
fun and : Bool -> Bool -> Bool
  = \(x : Bool) (y : Bool) . if @Bool x then y else False

fun eqInt : Integer -> Integer -> Bool
  = \(x : Integer) (y : Integer) . x == y

fun eqString : String -> String -> Bool
  = \(x : String) (y : String) . x ~~ y

data List (a : Type)
  = Nil : List a
  | Cons : a -> List a -> List a

fun foldr : all (a : Type)(r : Type) . (a -> r -> r) -> r -> List a -> r
  = /\(a : Type)(r : Type) . \(f : a -> r -> r) (e : r) (l : List a)
  . match_List @a l @r
      e
      (\(x : a) (xs : List a) . f x (foldr @a @r f e xs))

fun listEq : all (a : Type) . (a -> a -> Bool) -> List a -> List a -> Bool
  = /\(a : Type) . \(eq : a -> a -> Bool) (x0 : List a) (y0 : List a)
  . match_List @a x0 @Bool
      (match_List @a y0 @Bool True (\(y : a) (ys : List a) . False))
      (\(x : a) (xs : List a) . match_List @a y0 @Bool False (\(y : a) (ys : List a) . and (eq x y) (listEq @a eq xs ys)))

data Pair (x : Type) (y : Type)
  = P : x -> y -> Pair x y

fun pairEq : all (a : Type)(b : Type) . (a -> a -> Bool) -> (b -> b -> Bool) -> Pair a b -> Pair a b -> Bool
  = /\(a : Type)(b : Type) . \(eqA : a -> a -> Bool) (eqB : b -> b -> Bool) (x : Pair a b) (y : Pair a b)
  . match_Pair @a @b x @Bool
      (\(x0 : a) (x1 : b) . match_Pair @a @b y @Bool
        (\(y0 : a) (y1 : b) . and (eqA x0 y0) (eqB x1 y1)))

data Maybe (x : Type)
  = Just : x -> Maybe x
  | Nothing : Maybe x

fun maybeSum : all (x : Type) . Maybe x -> Maybe x -> Maybe x
  = /\ (x : Type) . \(mx : Maybe x)(my : Maybe x)
  . match_Maybe @x mx @(Maybe x)
      (\(jx : x) . Just @x jx)
      my

data KVMap (k : Type) (v : Type)
  = KV : List (Pair k v) -> KVMap k v

fun toList : all (k : Type)(v : Type) . KVMap k v -> List (Pair k v)
  = /\(k : Type)(v : Type) . \(m : KVMap k v) . match_KVMap @k @v m @(List (Pair k v)) (\(x : List (Pair k v)) . x)

fun lkupOne : all (k : Type)(v : Type) . (k -> Bool) -> Pair k v -> Maybe v
  = /\(k : Type)(v : Type) . \(predi : k -> Bool)(m : Pair k v)
  . match_Pair @k @v m @(Maybe v)
      (\(fst : k) (snd : v) . if @(Maybe v) predi fst then Just @v snd else Nothing @v)

fun lkup : all (k : Type)(v : Type) . (k -> k -> Bool) -> KVMap k v -> k -> Maybe v
  = /\(k : Type)(v : Type) . \(eq : k -> k -> Bool)(m : KVMap k v) (tgt : k)
  . match_KVMap @k @v m @(Maybe v)
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
data TxInfo
  = MkTxInfo : List TxOut -> List TxOut -> Value -> Value -> TxInfo

-- Analogous to Plutus assetClassValueOf
fun assetClassValueOf : Value -> Pair String String -> Integer
  = \(v : Value) (ac : Pair String String)
  . match_Pair @String @String ac @Integer
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
fun minSwap_isUnity : Value -> Pair String String -> Bool
  = \(v : Value) (ac : Pair String String) . assetClassValueOf v ac == 1

-- The correct spec for that should be exactly what we wrote in our blogpost:
--
-- > isUnity :: Value -> AssetClass -> Bool
-- > isUnity v c = Map.lookup curr (getValue v) == Just (Map.fromList [(tok, 1)])
-- >  where (curr, tok) = unAssetClass c
--
-- In our example language, that gets a little more verbose! :P
fun correct_isUnity : Value -> Pair String String -> Bool
  = \(v : Value) (ac : Pair String String)
  . match_Pair @String @String ac @Bool
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
fun example_ac : Pair String String
  = P @String @String "currency" "token"

-- And the infamous validator, slightly simplified:
fun validator : TxInfo -> Bool
  = \(tx : TxInfo)
    . match_TxInfo tx @Bool
      (\(inputs : List TxOut) (outputs : List TxOut) (fee : Value) (mint : Value). 
        minSwap_isUnity mint example_ac)

-- And the infamous validator, slightly simplified:
fun correct_validator : TxInfo -> Bool
  = \(tx : TxInfo)
    . match_TxInfo tx @Bool
      (\(inputs : List TxOut) (outputs : List TxOut) (fee : Value) (mint : Value). 
        correct_isUnity mint example_ac)

fun main : Integer = 42
|]
