{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Symbolic.ProveSpec (tests) where

import Control.Monad.Reader
import Data.Default
import Data.Maybe (isJust)
import Language.Pirouette.Example
import qualified Language.Pirouette.Example.IsUnity as IsUnity
import Language.Pirouette.Example.StdLib (stdLib)
import Pirouette.Monad
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.EvalUtils
import Pirouette.Symbolic.ProveSpec.Internal
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax
import Pirouette.Transformations (elimEvenOddMutRec)
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.EtaExpand
import Pirouette.Transformations.Monomorphization
import qualified PureSMT
import Test.Tasty
import Test.Tasty.HUnit

add1 :: (PrtUnorderedDefs Ex, Type Ex, Term Ex)
add1 =
  ( [prog|
add1 : Integer -> Integer
add1 x = x + 1

greaterThan0 : Integer -> Bool
greaterThan0 x = 0 < x

greaterThan1 : Integer -> Bool
greaterThan1 x = 1 < x
  |],
    [ty|Integer|],
    [term| \(x : Integer) . add1 x |]
  )

input0Output0 :: (Term Ex, Term Ex)
input0Output0 =
  ( [term| \(result : Integer) (x : Integer) . greaterThan0 result |],
    [term| \(result : Integer) (x : Integer) . greaterThan0 x |]
  )

input0Output1 :: (Term Ex, Term Ex)
input0Output1 =
  ( [term| \(result : Integer) (x : Integer) . greaterThan1 result |],
    [term| \(result : Integer) (x : Integer) . greaterThan0 x |]
  )

-- This is a small example taken from O'Hearn's paper; besides being interesting for
-- testing conditionals, it is also interesting in and of itself. This is the example:
--
-- > [z == 11]
-- > if (even x) {
-- >   if (odd y) {
-- >     z == 42
-- >   }
-- > }
-- > [z == 42]
--
-- Do you think the IL triple above is satisfiable? Surprisingly, it's not. In the imperative setting,
-- the statement @[P] f [Q]@ means that forall state s1 satisfying @Q@, there exists s0 such that s1 is reachable
-- from s0 by f and s0 satisfies @P@. With that in mind, the state @[(z, 42), (x, 3), (y, 2)]@ satisfies @Q@
-- and, albeit reachable, it is not reachable from a state satisfying the precondition @z == 11@.
-- Therefore the IL triple is falsifiable and we'd expect such a counterexample from our tool.
-- A IL triple really /means/ (def 1 from the IL paper):
--
-- > [P] f [Q] <=> { s' | s' \in Q } \subseteq { s' | exists s \in P . (s, s') \in f }
--
-- Which makes it obvious that the IL triple above is not sat. The state @[(z, 42), (x, 3), (y, 2)]@ satisfies Q,
-- but its not an element of { s' | exists s \in P . (s, s') \in f } because all elements of that set satisfy z == 11.
-- If we enrich our postcondition to read:
--
-- > [z == 42 && even x && odd y]
--
-- Now we have a valid IL triple, and this provides an interesting test case for pirouette.
-- Firstly, though, we have to translate the semantics of triples. In a pure setting we have
-- no notion of reachability, only termination. In fact, say that @f@ is a purely functional
-- expression (i.e., only reads from the state and returns a value), now assume @o@ is a fresh
-- name; the program @o = f@ can be seen as a binary relation of states: @{ (s , (o , valof s f):s) | forall s }@
-- Where @valof s f@ denotes the value of @f@ evaluated at state @s@.
--
-- Now, lets look at what a IL triple over @res = f@ would /mean/:
--
-- > [P] o = f [Q] <=> { s' | s' \in Q } \subseteq { s' | exists s \in P . (s, s') \in "o = f" }
-- >               <=> { s' | s' \in Q } \subseteq { (o, valof s f) : s | s \in P }
--
-- Note, in particular, that @Q@ makes no attempt to estabilish that its argument @s'@ has
-- any connection whatsoever with the state in which @f@ is computed. If @Q@ does not mention
-- the @o@ variable at all, then it is reasonable to weaken the above inequality to:
--
-- > { (o, valof s f):s | s \in Q } \subseteq { (o, valof s f):s | s \in P } <=> Q `implies` P
--
-- Which gets further simplified to @Q `implies` P@.
--
-- If @Q@ does mention the result, @Q@ can be seen as a relation between
-- the input @s@ and the output @valof s f@, which would let us write:
--
-- > { (o, valof s f):s | forall s . Q s (valof f s) } \subseteq { (o, valof r f):r | r \in P }
--
-- (We alpha-converted one of the sets to avoid name clashing)
-- Now, expanding the meaning of @\subseteq@:
--
-- >     forall s . Q s (valof f s) `implies` (o, valof s f):s \in { (o, valof r f):r | r \in P }
-- > <=> forall s . Q s (valof f s) `implies` (exists r . r \in P && r == s && valof s f == valof r f)
-- > <=> forall s . Q s (valof f s) `implies` s \in P
--
-- Now, we rename @s@ to @i@ to make it clear that it is, in a way, the input to the pure function @f@,
-- we arrive at:
--
-- > SEM1: [P] f [Q] <=> forall i . Q i (f i) `implies` P i
--
-- With a purely functional characterization, we can craft an example similar to
-- the code block given by O'Hearn on their paper to Haskell:
--
-- > ohearn :: (Integer, Integer) -> (Integer, Integer)
-- > ohearn x y
-- >   | even x = (x, 42)
-- >   | otherwise = (x, y)
--
-- Now, if we ask the question of whether or not the following triple is valid:
--
-- > [\(x, y) -> y == 11] ohearn [\(rx, ry) (x, y) -> ry == 42]
--
-- Or, in other words:
--
-- > forall (x, y) . (_, 42) = ohearn (x, y) `implies` y == 11
--
-- We can easily find a counterexample with a similar model, take @x@ to be an odd
-- number and @y@ to be 42: f (3, 42) = (3, 42) && y /= 11
-- Again, strengthtening the postcondition gives us a valid triple:
--
-- > [\(x, y) -> y == 11] ohearn [\(rx, ry) (x, y) -> even x && ry == 42]
--
-- # A Pitfal: forgetting infromation about the input
--
-- Curiously enough, the SEM1 formulation above that we derived above is suspiciously
-- similar to another one, which we could have used instead:
--
-- > SEM2: [P] f [Q] <=> { o | exists i . o = f i && Q i o } \subseteq { f i | P i }
--
-- Yet SEM2 expands to
--
-- >    forall x . x \in { o | exists i . o = f i && Q i o } `implies` x \in { f i | P i }
-- > == forall x . (exists i1 . x = f i1 && Q i1 x) `implies` (exists i2 . P i2 && x = f i2)
-- > == forall x i1 . x = f i1 && Q i1 x `implies` (exists i2 . P i2 && x = f i2)
-- > == forall i1 . Q i1 (f i1) `implies` (exists i2 . P i2 && f i1 = f i2)
--
-- We have that SEM1 implies SEM2 but not the other way around, only for injective functions.
-- This happened because we dropped information about which inputs originated which outputs
-- when we restricted ourselves to sets of outputs. Because both post and pre-conditions are represented as
-- sets of states in the stateful calculus, the subset relation forces the variables not
-- modified from pre to post state to remain the same, in other words, the pre and post-conditions
-- are sets of outputs AND inputs:
--
-- > SEM3: [P] f [Q] <=> { (f i, i) | Q i (f i) } \subseteq { (f i, i) | P i }
--
-- Now we have that SEM1 is equivalent to SEM3

conditionals1 :: (PrtUnorderedDefs Ex, Type Ex, Term Ex)
conditionals1 =
  ( [prog|
data Delta = D : Integer -> Integer -> Delta

fst : Delta -> Integer
fst x = match_Delta x @Integer (\(a : Integer) (b : Integer) . a)

snd : Delta -> Integer
snd x = match_Delta x @Integer (\(a : Integer) (b : Integer) . b)

even : Integer -> Bool
even x = if @Bool x == 0 then True else odd (x - 1)

odd : Integer -> Bool
odd x = if @Bool x == 0 then False else even (x - 1)

and : Bool -> Bool -> Bool
and x y = if @Bool x then y else False

ohearn : Delta -> Delta
ohearn xy =
  if @Delta even (fst xy)
  then D (fst xy) 42
  else xy
  |],
    [ty|Delta|],
    [term| \(x : Delta) . ohearn x |]
  )

condWrongTriple :: (Term Ex, Term Ex)
condWrongTriple =
  ( [term| \(result : Delta) (x : Delta) . snd result == 42 |],
    [term| \(result : Delta) (x : Delta) . snd x == 11 |]
  )

condCorrectTriple :: (Term Ex, Term Ex)
condCorrectTriple =
  ( [term| \(result : Delta) (x : Delta) . (and (snd result == 42) (even (fst result))) |],
    [term| \(result : Delta) (x : Delta) . snd x == 11 |]
  )

ohearnTest :: TestTree
ohearnTest =
  testGroup
    "OHearn"
    [ testCase "[y == 11] ohearn [snd result == 42] counter" $
        let test = isCounterWith $ \(Model p) ->
              case lookup (PureSMT.Atom "pir_x") p of
                Just (PureSMT.Other (PureSMT.List [PureSMT.Atom "pir_D", PureSMT.Atom fstX, _])) ->
                  odd (read fstX)
                _ -> False
         in exec (proveAny def test) conditionals1 condWrongTriple `satisfies` isJust
        -- testCase "[y == 11] ohearn [snd result == 42 && even (fst result)] verified" $
        --   execWithFuel 50 conditionals1 condCorrectTriple `pathSatisfies` all (isNoCounter .||. ranOutOfFuel)
    ]

-- We didn't have much success with builtins integers; let me try the same with peano naturals:

conditionals1Peano :: (PrtUnorderedDefs Ex, Type Ex, Term Ex)
conditionals1Peano =
  ( [prog|
data Nat = Z : Nat | S : Nat -> Nat

eq : Nat -> Nat -> Bool
eq x y =
  match_Nat x @Bool
    (match_Nat y @Bool True (\(yy : Nat) . False))
    (\(xx : Nat) . match_Nat y @Bool False (\(yy : Nat) . eq xx yy))

even : Nat -> Bool
even x = match_Nat x @Bool True odd

odd : Nat -> Bool
odd x = match_Nat x @Bool False even

data Delta = D : Nat -> Nat -> Delta

fst : Delta -> Nat
fst x = match_Delta x @Nat (\(a : Nat) (b : Nat) . a)

snd : Delta -> Nat
snd x = match_Delta x @Nat (\(a : Nat) (b : Nat) . b)

and : Bool -> Bool -> Bool
and x y = if @Bool x then y else False

ohearn : Delta -> Delta
ohearn xy =
  if @Delta even (fst xy)
  then D (fst xy) (S (S Z))
  else xy
  |],
    [ty|Delta|],
    [term| \(x : Delta) . ohearn x |]
  )

condWrongTriplePeano :: (Term Ex, Term Ex)
condWrongTriplePeano =
  ( [term| \(result : Delta) (x : Delta) . eq (snd result) (S (S Z)) |],
    [term| \(result : Delta) (x : Delta) . eq (snd x) (S Z)  |]
  )

condCorrectTriplePeano :: (Term Ex, Term Ex)
condCorrectTriplePeano =
  ( [term| \(result : Delta) (x : Delta) . (and (eq (snd result) (S (S Z))) (even (fst result))) |],
    [term| \(result : Delta) (x : Delta) . eq (snd x) (S Z) |]
  )

-- XXX: The following tests are hitting the bug on Pirouette.SMT.Constraints, line 196

ohearnTestPeano :: TestTree
ohearnTestPeano =
  testGroup
    "OHearn Peano"
    [ testCase "[y == 1] ohearn-peano [snd result == 2] counter" $
        let test = isCounterWith $ \(Model p) ->
              case lookup (PureSMT.Atom "pir_x") p of
                Just (PureSMT.Other (PureSMT.List [PureSMT.Atom "pir_D", fstX, _])) ->
                  fstX == PureSMT.List [PureSMT.Atom "pir_S", PureSMT.Atom "pir_Z"]
                _ -> False
         in exec (proveAny def test) conditionals1Peano condWrongTriplePeano `satisfies` isJust
        -- testCase "[y == 1] ohearn-peano [snd result == 2 && even (fst result)] verified" $
        --   exec conditionals1Peano condCorrectTriplePeano `pathSatisfies` all isVerified
    ]

switchSides :: (Term Ex, Term Ex) -> (Term Ex, Term Ex)
switchSides (assume, prove) = (prove, assume)

tests :: [TestTree]
tests =
  [ testGroup
      "incorrectness triples"
      [ testCase "[input > 0] add 1 [result > 0] counter" $
          exec (proveUnbounded def) add1 input0Output0 `pathSatisfies` (isSingleton .&. all isCounter),
        testCase "[input > 0] add 1 [result > 1] verified" $
          exec (proveUnbounded def) add1 input0Output1 `pathSatisfies` (isSingleton .&. all isVerified),
        testCase "[isNothing x] isJust x [not result] verified" $
          exec
            (proveUnbounded def)
            (stdLib, [ty|Bool|], [term|\(x:Maybe Integer) . isJust @Integer x|])
            ([term|\(r:Bool) (x:Maybe Integer) . not r|], [term|\(r:Bool) (x:Maybe Integer) . isNothing @Integer x|])
            `pathSatisfies` (all isNoCounter .&. any isVerified),
        testCase "[isJust x] isJust x [not result] counter" $
          exec
            (proveUnbounded def)
            (stdLib, [ty|Bool|], [term|\(x:Maybe Integer) . isJust @Integer x|])
            ([term|\(r:Bool) (x:Maybe Integer) . not r|], [term|\(r:Bool) (x:Maybe Integer) . isJust @Integer x|])
            `pathSatisfies` any isCounter
      ],
    testGroup
      "Hoare triples"
      [ testCase "{input > 0} add 1 {result > 0} verified" $
          exec (proveUnbounded def) add1 (switchSides input0Output0) `pathSatisfies` (isSingleton .&. all isVerified),
        testCase "{input > 0} add 1 {result > 1} verified" $
          exec (proveUnbounded def) add1 (switchSides input0Output1) `pathSatisfies` (isSingleton .&. all isVerified)
      ],
    ohearnTest,
    ohearnTestPeano,
    isUnityTest
  ]

-- * IsUnity example

isUnity :: (PrtUnorderedDefs Ex, Type Ex, Term Ex)
isUnity =
  ( IsUnity.definitions,
    [ty|Bool|],
    [term| \(tx : TxInfo) . validator tx |]
  )

-- Now we estabilish the incorrectness triple that says:
--
-- > [ \v -> correct_isUnity example_ac v ] validator v [ \r _ -> r ]
--
-- In other words, it only validates if @v@ is correct. We expect
-- a counterexample out of this.
condIsUnity :: (Term Ex, Term Ex)
condIsUnity =
  ( [term| \(result : Bool) (tx : TxInfo) . result |],
    [term| \(result : Bool) (tx : TxInfo) . correct_validator tx |]
  )

execFull ::
  (Problem Ex -> ReaderT (PrtOrderedDefs Ex) IO a) ->
  (PrtUnorderedDefs Ex, Type Ex, Term Ex) ->
  (Term Ex, Term Ex) ->
  IO a
execFull toDo (prog0, tyRes, fn) (assume, toProve) = do
  -- liftIO $ writeFile "prog0" (show $ pretty $ prtUODecls prog0)
  let prog1 = monomorphize' prog0
  -- liftIO $ writeFile "prog1" (show $ pretty $ prtUODecls prog1)
  let decls = defunctionalize' $ etaExpandAll' prog1
  -- liftIO $ writeFile "final" (show $ pretty $ prtUODecls decls)
  let orderedDecls = elimEvenOddMutRec decls
  flip runReaderT orderedDecls $
    toDo (Problem tyRes fn assume toProve)

isUnityTest :: TestTree
isUnityTest =
  testGroup
    "isUnity Bug"
    [ testCase "[correct_isUnity v] validate [\\r _ -> r] counter" $
        execFull (proveAny def isCounter) isUnity condIsUnity `satisfies` isJust
    ]
