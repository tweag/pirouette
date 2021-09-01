{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Pirouette.TLA.Syntax where

import           Pirouette.Term.Syntax (Name(..))

import qualified Language.TLAPlus.Syntax as TLA
import qualified Language.TLAPlus.Parser as TLA

import qualified Data.Text as T
import qualified Text.ParserCombinators.Parsec.Pos as PPos

-- The default infos, used everywhere

di :: TLA.AS_InfoE
di = TLA.di

diu :: TLA.AS_InfoU
diu = PPos.newPos "" 0 0

-- * TLA Identifiers

class TLAIdent n where
  toString         :: n -> String

  tlaIdent         :: n -> TLA.AS_Expression
  tlaIdent         = tlaIdentPrefixed ""

  tlaIdentPrefixed :: String -> n -> TLA.AS_Expression
  tlaIdentPrefixed pref s = TLA.AS_Ident di [] (pref ++ toString s)

instance TLAIdent Name where
  toString (Name n u) = T.unpack n ++ maybe "" show u

instance TLAIdent String where
  toString = id

instance TLAIdent n => TLAIdent (String , n) where
  toString (s, n) = s ++ toString n

-- * TLA Smart Constructors

-- |Creates a disjunction from a list of expressions while distributing
-- and associating disjunctions. That is,
--
-- > tlaOr [TLA.AS_LOR l, e] = TLA.AS_LOR (l ++ [e])
--
tlaOr :: [TLA.AS_Expression] -> TLA.AS_Expression
tlaOr [e] = e
tlaOr l   =
  let (ors, others) = span isOr l in
  TLA.AS_LOR di (concatMap extractExp ors ++ others)
  where
    isOr (TLA.AS_LOR _ _) = True
    isOr _ = False

    extractExp (TLA.AS_LOR _ l) = l

-- |Creates a conjunction from a list of expressions, analogous to
-- 'tlaOr'
tlaAnd :: [TLA.AS_Expression] -> TLA.AS_Expression
tlaAnd [e] = e
tlaAnd l   =
  let (ands, others) = span isAnd l in
  TLA.AS_LAND di (concatMap extractExp ands ++ others)
  where
    isAnd (TLA.AS_LAND _ _) = True
    isAnd _ = False

    extractExp (TLA.AS_LAND _ l) = l

-- |Applies a TLA Operator to a list of arguments
tlaOpApp :: TLA.AS_Expression -> [TLA.AS_Expression] -> TLA.AS_Expression
tlaOpApp n [] = n
tlaOpApp n l  = TLA.AS_OpApp di n l

tlaOpPostApp :: TLA.AS_Expression -> [TLA.AS_Expression] -> TLA.AS_Expression
tlaOpPostApp (TLA.AS_OpApp _ n ls) l = TLA.AS_OpApp di n (ls ++ l)
tlaOpPostApp n                     l = tlaOpApp n l

-- |Applies a TLA Function to a list of arguments
tlaFunApp :: TLA.AS_Expression -> [TLA.AS_Expression] -> TLA.AS_Expression
tlaFunApp f [] = f
tlaFunApp f l  = tlaInfix TLA.AS_FunApp f (TLA.AS_FunArgList di l)

-- |Creates a primed identifier
tlaPrime :: (TLAIdent name) => name -> TLA.AS_Expression
tlaPrime n = TLA.AS_PostfixOP di TLA.AS_Prime (tlaIdent n)

tlaIf :: TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaIf = TLA.AS_IF di

tlaInfix :: TLA.AS_InfixOp -> TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaInfix = TLA.AS_InfixOP di

tlaPrefix :: TLA.AS_PrefixOp -> TLA.AS_Expression -> TLA.AS_Expression
tlaPrefix = TLA.AS_PrefixOP di

tlaEq :: TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaEq = tlaInfix TLA.AS_EQ

tlaGreater :: TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaGreater = tlaInfix TLA.AS_GT

tlaNot :: TLA.AS_Expression -> TLA.AS_Expression
tlaNot = tlaPrefix TLA.AS_Not

-- * Declaring Operators

tlaOpDef :: TLA.AS_Expression -> [TLA.AS_Expression] -> TLA.AS_Expression -> TLA.AS_UnitDef
tlaOpDef n args = TLA.AS_OperatorDef diu False (TLA.AS_OpHead n args)

tlaOpDef' :: (TLAIdent name, TLAIdent n)
          => name -> [n] -> TLA.AS_Expression -> TLA.AS_UnitDef
tlaOpDef' n args = tlaOpDef (tlaIdent n) (map tlaIdent args)

tlaAssign :: TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_UnitDef
tlaAssign = flip tlaOpDef []

tlaLet :: [TLA.AS_UnitDef] -> TLA.AS_Expression -> TLA.AS_Expression
tlaLet = TLA.AS_Let di

tlaFunType :: TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaFunType = TLA.AS_FunctionType di

tlaProj :: TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaProj = tlaInfix TLA.AS_DOT

tlaProj' :: (TLAIdent n) => TLA.AS_Expression -> n -> TLA.AS_Expression
tlaProj' t = tlaInfix TLA.AS_DOT t . tlaIdent

tlaUnion :: TLA.AS_Expression -> TLA.AS_Expression
tlaUnion = TLA.AS_PrefixOP di TLA.AS_UNION

tlaUnions :: [TLA.AS_Expression] -> TLA.AS_Expression
tlaUnions []  = tlaEmptySet
tlaUnions [x] = x
tlaUnions xs  = tlaUnion $ TLA.AS_DiscreteSet di xs

tlaRecordType :: [(String, TLA.AS_Expression)] -> TLA.AS_Expression
tlaRecordType l =
  TLA.AS_RecordType di
    (map (\(s,e) -> TLA.AS_RecordElementType di (TLA.AS_Field s) e) l)

tlaMinus :: TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaMinus = tlaInfix TLA.AS_Minus

tlaSingleton :: TLA.AS_Expression -> TLA.AS_Expression
tlaSingleton e = TLA.AS_DiscreteSet di [e]

tlaEmptySet :: TLA.AS_Expression
tlaEmptySet = TLA.AS_DiscreteSet di []

-- We translate elements of inductive datatypes as records.
-- Here are the expressions and fields associated to this transformation.

onType :: TLA.AS_Expression
onType = tlaIdent "type"

onCons :: TLA.AS_Expression
onCons = tlaIdent "cons"

onArg :: Int -> TLA.AS_Expression
onArg i = tlaIdent ("arg" ++ show i)

argField :: Int -> String
argField i = "arg" ++ show i

-- Encoding elements of builtin types to TLA

tlaString :: TLAIdent n => n -> TLA.AS_Expression
tlaString n = TLA.AS_StringLiteral di (toString n)

tlaNum :: Int -> TLA.AS_Expression
tlaNum i = TLA.AS_Num di (toInteger i)

tlaBool :: Bool -> TLA.AS_Expression
tlaBool = TLA.AS_Bool di
