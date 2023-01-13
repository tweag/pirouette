{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
-- -l has the effect of causing the TH interpreter to try loading
-- z3 to resolve otherwise undefined symbols
{-# OPTIONS_GHC -lz3 #-}

module Language.Pirouette.Example.StdLib where

import Language.Haskell.TH.Quote
import Language.Pirouette.Example
import Language.Pirouette.QuasiQuoter.Internal (maybeQ, parseQ, quoter, trQ)
import Language.Pirouette.QuasiQuoter.Syntax
import Language.Pirouette.QuasiQuoter.ToTerm
import Pirouette.Monad
import Pirouette.Term.TypeChecker (typeCheckDecls)
import Text.Megaparsec

booleans :: PrtUnorderedDefs Ex
booleans =
  [progNoTC|
and : Bool -> Bool -> Bool
and x y = if @Bool x then y else False

or : Bool -> Bool -> Bool
or x y = if @Bool x then True else y
|]

lists :: PrtUnorderedDefs Ex
lists =
  [progNoTC|
data List a
  = Nil : List a
  | Cons : a -> List a -> List a

foldr : forall a r . (a -> r -> r) -> r -> List a -> r
foldr @a @r f e l =
  match_List @a l @r
    e
    (\(x : a) (xs : List a) . f x (foldr @a @r f e xs))

eqList :
  forall a .
  (a -> a -> Bool) ->
  List a -> List a -> Bool
eqList @a eq x0 y0 =
  match_List @a x0 @Bool
    (match_List @a y0 @Bool
      True
      (\(y : a) (ys : List a) . False))
    (\(x : a) (xs : List a) .
      match_List @a y0 @Bool
        False
        (\(y : a) (ys : List a) . and (eq x y) (eqList @a eq xs ys)))

any : forall a . (a -> Bool) -> List a -> Bool
any @a p xs =
  match_List @a xs @Bool
    False
    (\(x : a) (xs2 : List a) . or (p x) (any @a p xs2))

all : forall a . (a -> Bool) -> List a -> Bool
all @a p xs =
  match_List @a xs @Bool
    True
    (\(x : a) (xs2 : List a) . and (p x) (all @a p xs2))
|]

stdLib :: PrtUnorderedDefs Ex
stdLib = unionPrtUODefs booleans lists

progWithStdLib :: QuasiQuoter
progWithStdLib = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseProgram @Ex) <* eof) str
  decls <- trQ (trProgram p0)
  let fullDefs = addDecls decls stdLib
      fullDecls = prtUODecls fullDefs
  _ <- maybeQ (typeCheckDecls fullDecls)
  [e|(PrtUnorderedDefs fullDecls)|]
