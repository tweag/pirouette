{-# LANGUAGE QuasiQuotes #-}

module Pirouette.Symbolic.Eval.Playground where

import Data.Default
import Language.Pirouette.Example
import Pirouette.Monad
import Pirouette.Symbolic.Eval.Anamorphism
import Pirouette.Symbolic.Eval.Catamorphism
import Pirouette.Symbolic.Eval.Types
import Pirouette.Term.Syntax

defs :: PrtUnorderedDefs Ex
defs =
  [prog|
data Nat
  = Zero : Nat
  | Suc : Nat -> Nat
  destructor Nat_match

fun add : Nat -> Nat -> Nat
  = \(n : Nat) (m : Nat) . Nat_match n @Nat m (\sn : Nat . Suc (add sn m))
|]

opts :: Options
opts = def {maxAssignments = 1}

x :: [Path Ex (TermMeta Ex SymVar)]
x = catamorphism defs opts (symbolically defs [term| \(n : Nat) . add n (Suc n) |])

xio :: IO ()
xio = mapM_ (\p -> putStrLn "Path:" >> putStrLn (prettyIndent p)) x
  where
    prettyIndent =
      unlines
        . map ("  " ++)
        . lines
        . show
        . pretty
