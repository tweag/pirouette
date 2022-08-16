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

add : Nat -> Nat -> Nat
add n m = Nat_match n @Nat m (\sn : Nat . Suc (add sn m))

isEven : Integer -> Bool
isEven n = if @Bool n == 0 then True else (if @Bool n == 1 then False else isEven (n - 2))
|]

opts :: Options
opts = def {maxAssignments = 1}

x :: [Path Ex (WHNFTerm Ex)]
x = catamorphism defs opts (symbolically defs [term| \(n : Integer) . isEven n |])

xio :: IO ()
xio = mapM_ (\p -> putStrLn "Path:" >> putStrLn (prettyIndent p)) x
  where
    prettyIndent =
      unlines
        . map ("  " ++)
        . lines
        . show
        . pretty
