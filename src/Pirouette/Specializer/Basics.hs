{-# LANGUAGE QuasiQuotes        #-}

module Pirouette.Specializer.Basics where

import Pirouette.Specializer.TypeDecl
import Pirouette.Term.Syntax
import Pirouette.TLA.Syntax

import Language.TLAPlus.Quasiquote (tla_e, tla_u)
import Language.TLAPlus.Syntax (AS_Expression)

import qualified Data.Text as T

boolSpzMatch t n [] _ exp
  | nameString n == T.pack "True"  = tlaAnd [t, exp]
  | nameString n == T.pack "False" = tlaAnd [tlaNot t, exp]

boolSpz :: TypeSpecializer
boolSpz = TypeSpecializer {
  spzSet = [tla_u|SetOfBool == BOOLEAN|],
  spzConstructors = [[tla_u|True == TRUE|], [tla_u|False == FALSE|]],
  spzDestructor = [tla_u|Bool_match(b,cT,cF) == IF b THEN cT ELSE cF|],
  spzMatch = boolSpzMatch
}

listSpzMatch t n [] _ exp
  | nameString n == T.pack "Nil"  = tlaAnd [tlaEq t [tla_e|<<>>|], exp]
listSpzMatch t n [x,tl] freeName exp
  | nameString n == T.pack "Cons" =
      tlaLet [tlaAssign freeName t] $
        tlaAnd
          [ tlaGreater (tlaOpApp (tlaIdent "Length") [freeName]) (tlaNum 0)
          , tlaLet
              [ tlaAssign (tlaIdent x) (tlaOpApp (tlaIdent "Head") [freeName])
              , tlaAssign (tlaIdent tl) (tlaOpApp (tlaIdent "Tail") [freeName])]
              exp
          ]

listSpz :: TypeSpecializer
listSpz = TypeSpecializer {
  spzSet = [tla_u|SetOfList(a) == UNION {[1..n -> a]: n \in 0..(MAXDEPTH - 1)}|],
  spzConstructors = [[tla_u|Nil == <<>>|], [tla_u|Cons(x,tl) == <<x>> \o tl|]],
  spzDestructor = [tla_u|Nil_match(l,cN,cC(_,_)) == IF l = <<>> THEN cN ELSE LET hd == Head(l) tl == Tail(l) IN cC(hd,tl)|],
  spzMatch = listSpzMatch
}

unitSpzMatch _ n [] _ exp
  | nameString n == T.pack "Unit1"  = exp

unitSpz :: TypeSpecializer
unitSpz = TypeSpecializer {
  spzSet = [tla_u|SetOfUnit0 == {{}}|],
  spzConstructors = [[tla_u|Unit1 == {}|]],
  spzDestructor = [tla_u|Unit_match(u,cU) == cU|],
  spzMatch = unitSpzMatch
}

tuple2SpzMatch t n [x,y] freeName exp
  | nameString n == T.pack "Tuple21" =
      tlaLet [tlaAssign freeName t] $
        tlaLet
          [ tlaAssign (tlaIdent x) (tlaFunApp freeName [tlaNum 1])
          , tlaAssign (tlaIdent y) (tlaFunApp freeName [tlaNum 2])]
          exp

tuple2Spz :: TypeSpecializer
tuple2Spz = TypeSpecializer {
  spzSet = [tla_u|SetOfTuple20(a,b) == a \X b|],
  spzConstructors = [[tla_u|Tuple21(x,y) == <<x, y>>|]],
  spzDestructor = [tla_u|Tuple2_match(t,cT(_,_)) == cT(t[1],t[2])|],
  spzMatch = tuple2SpzMatch
}
