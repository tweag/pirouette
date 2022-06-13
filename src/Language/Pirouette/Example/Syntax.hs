{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Pirouette.Example.Syntax where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Data
import Data.Foldable
import qualified Data.Map as M
import Data.Maybe (isJust)
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Pirouette.Monad (termIsMeta)
import Pirouette.SMT
import qualified Pirouette.SMT.SimpleSMT as SimpleSMT
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils (monoNameSep)
import Language.Pirouette.QuasiQuoter.Syntax
import Prettyprinter (dquotes)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Set as S

-- * AST

-- ** Pirouette Builtins

-- $pirouettebuiltins
--
-- The following types will be used as the /BuiltinTypes/, /BuiltinTerms/ and /Constants/
-- of a Pirouette /LanguageBuiltins/ class. Yet, because Pirouette terms use de Bruijn indices,
-- we'll parse an intermediate, simpler AST, then translate to a Pirouette Term.

data ExType
  = TyInteger
  | TyBool
  | TyString
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

instance Pretty ExType where
  prettyPrec _ TyInteger = "Integer"
  prettyPrec _ TyBool = "Bool"
  prettyPrec _ TyString = "String"

data ExTerm
  = TermAdd
  | TermSub
  | TermLt
  | TermEq
  | TermStrEq
  | TermIte
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

exTermIsArithOp :: ExTerm -> Bool
exTermIsArithOp TermAdd = True
exTermIsArithOp TermSub = True
exTermIsArithOp TermLt = True
exTermIsArithOp TermEq = True
exTermIsArithOp _ = False

exTermIsStringOp :: ExTerm -> Bool
exTermIsStringOp TermStrEq = True
exTermIsStringOp _ = False

instance Pretty ExTerm where
  prettyPrec _ TermAdd = "add"
  prettyPrec _ TermSub = "sub"
  prettyPrec _ TermLt = "<"
  prettyPrec _ TermEq = "=="
  prettyPrec _ TermStrEq = "string-eq"
  prettyPrec _ TermIte = "ite"

data ExConstant
  = ConstInt Integer
  | ConstBool Bool
  | ConstString String
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

instance Pretty ExConstant where
  prettyPrec _ (ConstInt n) = pretty n
  prettyPrec _ (ConstBool b) = pretty b
  prettyPrec _ (ConstString s) = dquotes $ pretty s

-- | The language builtins definition
data Ex deriving (Data)

instance LanguageBuiltins Ex where
  type BuiltinTypes Ex = ExType
  type BuiltinTerms Ex = ExTerm
  type Constants Ex = ExConstant

instance LanguageParser Ex where
  parseBuiltinType =
   label "Builtin type" $
    (TyInteger <$ symbol "Integer")
      <|> (TyBool <$ symbol "Bool")
      <|> (TyString <$ symbol "String")

  parseBuiltinTerm = fail "all builtin terms of Ex are parsed through the operator table"

  operators =
        [[ InfixR (symbol "+" >> return (exprBinApp TermAdd)),
          InfixR (symbol "-" >> return (exprBinApp TermSub))
        ],
        [ InfixN (symbol "<" >> return (exprBinApp TermLt)),
          InfixN (symbol "==" >> return (exprBinApp TermEq)),
          InfixN (symbol "~~" >> return (exprBinApp TermStrEq))
        ]]

  parseConstant = label "Constant" $
    asum
      [ ConstInt <$> try integer,
        ConstBool <$> try parseBoolean,
        ConstString <$> try stringLiteral
      ]
    where
      parseBoolean = (True <$ symbol "True") <|> (False <$ symbol "False")
      integer :: Parser Integer
      integer = L.lexeme spaceConsumer L.decimal
      -- copied from
      -- https://hackage.haskell.org/package/megaparsec/docs/Text-Megaparsec-Char-Lexer.html#v:charLiteral
      stringLiteral :: Parser String
      stringLiteral = L.lexeme spaceConsumer (char '"' >> manyTill L.charLiteral (char '"'))

  reservedNames = S.fromList ["True", "False"]
  reservedTypeNames = S.fromList ["Integer", "Bool", "Type"]

  ifThenElse ty c t e = SystF.App (SystF.Free $ Builtin TermIte) $ SystF.TyArg ty : map SystF.TermArg [c, t, e]

instance LanguageBuiltinTypes Ex where
  typeOfBottom = error "no bottom type in Ex"
  typeOfConstant (ConstInt _) = TInt
  typeOfConstant (ConstBool _) = TBool
  typeOfConstant (ConstString _) = TString
  typeOfBuiltin TermAdd = SystF.TyFun TInt (SystF.TyFun TInt TInt)
  typeOfBuiltin TermSub = SystF.TyFun TInt (SystF.TyFun TInt TInt)
  typeOfBuiltin TermLt = SystF.TyFun TInt (SystF.TyFun TInt TBool)
  typeOfBuiltin TermEq = SystF.TyFun TInt (SystF.TyFun TInt TBool)
  typeOfBuiltin TermStrEq = SystF.TyFun TString (SystF.TyFun TString TBool)
  typeOfBuiltin TermIte =
    SystF.TyAll (SystF.Ann "a") SystF.KStar $
      SystF.TyFun TBool (SystF.TyFun a (SystF.TyFun a a))
    where
      a = SystF.TyPure $ SystF.Bound (SystF.Ann "a") 0

pattern TInt :: TypeMeta Ex meta
pattern TInt = SystF.TyPure (SystF.Free (TyBuiltin TyInteger))

pattern TBool :: TypeMeta Ex meta
pattern TBool = SystF.TyPure (SystF.Free (TyBuiltin TyBool))

pattern TString :: TypeMeta Ex meta
pattern TString = SystF.TyPure (SystF.Free (TyBuiltin TyString))

instance LanguageSMT Ex where
  translateBuiltinType TyInteger = SimpleSMT.tInt
  translateBuiltinType TyBool = SimpleSMT.tBool
  translateBuiltinType TyString = SimpleSMT.tString
  translateConstant (ConstInt n) = SimpleSMT.int n
  translateConstant (ConstBool b) = SimpleSMT.bool b
  translateConstant (ConstString s) = SimpleSMT.string s
  translateBuiltinTerm TermAdd [x, y] = Just $ SimpleSMT.add x y
  translateBuiltinTerm TermSub [x, y] = Just $ SimpleSMT.sub x y
  translateBuiltinTerm TermLt [x, y] = Just $ SimpleSMT.lt x y
  translateBuiltinTerm TermEq [x, y] = Just $ SimpleSMT.eq x y
  translateBuiltinTerm TermStrEq [x, y] = Just $ SimpleSMT.eq x y
  -- DO NOT TRANSLATE THIS TO 'ite',
  -- This should be taken care by symbolic evaluation branching,
  -- since it is in fact like 'match'
  translateBuiltinTerm TermIte [_, _c, _t, _e] = Nothing
  translateBuiltinTerm _ _ = Nothing

  -- they are stuck if they are constants, ot a not-ite builtin
  isStuckBuiltin e
    | isConstant e = True
  isStuckBuiltin (SystF.App (SystF.Free (Builtin op)) args)
    | exTermIsArithOp op || exTermIsStringOp op =
      let args' = map (\(SystF.TermArg a) -> a) args
       in all isStuckBuiltin args' && not (all isConstant args')
  isStuckBuiltin tm = isJust (termIsMeta tm)

pattern BConstant :: Bool -> TermMeta Ex meta
pattern BConstant b = SystF.App (SystF.Free (Constant (ConstBool b))) []

pattern BTrue :: TermMeta Ex meta
pattern BTrue = BConstant True

pattern BFalse :: TermMeta Ex meta
pattern BFalse = BConstant False

pattern IConstant :: Integer -> TermMeta Ex meta
pattern IConstant n = SystF.App (SystF.Free (Constant (ConstInt n))) []

pattern SConstant :: String -> TermMeta Ex meta
pattern SConstant s = SystF.App (SystF.Free (Constant (ConstString s))) []

isConstant :: TermMeta Ex meta -> Bool
isConstant (IConstant _) = True
isConstant (BConstant _) = True
isConstant (SConstant _) = True
isConstant _ = False

instance LanguageSMTBranches Ex where
  -- translate arithmetic operations applied to constants
  branchesBuiltinTerm op _translator [SystF.TermArg (IConstant x), SystF.TermArg (IConstant y)]
    | exTermIsArithOp op =
      pure $ Just [Branch mempty (apply op)]
    where
      apply TermAdd = IConstant (x + y)
      apply TermSub = IConstant (x - y)
      apply TermLt = BConstant (x < y)
      apply TermEq = BConstant (x == y)
      apply _ = error "this should never happen"
  -- translate string equality applied to constants
  branchesBuiltinTerm TermStrEq _translator [SystF.TermArg (SConstant x), SystF.TermArg (SConstant y)] =
    pure $ Just [Branch mempty (BConstant (x == y))]
  -- the gist of it: branch when we find an 'if'
  branchesBuiltinTerm
    TermIte
    _translator
    (SystF.TyArg _ : SystF.TermArg c : SystF.TermArg t : SystF.TermArg e : excess) =
      let isEq TermEq = True
          isEq TermStrEq = True
          isEq _ = False
          t' = t `SystF.appN` excess
          e' = e `SystF.appN` excess
       in case c of
            BTrue -> pure $ Just [Branch (And []) t]
            BFalse -> pure $ Just [Branch (And []) e]
            SystF.App (SystF.Free (Builtin eq)) [SystF.TermArg x, SystF.TermArg y]
              -- try to generate the best type of constraint
              -- from the available equality ones
              | isEq eq,
                Just x1 <- termIsMeta x,
                Just y1 <- termIsMeta y ->
                pure $
                  Just
                    [ -- either they are equal
                      Branch (And [VarEq x1 y1]) t',
                      -- or they are not
                      Branch (And [NonInlinableSymbolNotEq x y]) e'
                    ]
              | isEq eq,
                Just x1 <- termIsMeta x,
                isStuckBuiltin y ->
                pure $
                  Just
                    [ -- either they are equal
                      Branch (And [Assign x1 y]) t',
                      -- or they are not
                      Branch (And [NonInlinableSymbolNotEq x y]) e'
                    ]
              | isEq eq,
                isStuckBuiltin x,
                Just y1 <- termIsMeta y ->
                pure $
                  Just
                    [ -- either they are equal
                      Branch (And [Assign y1 x]) t',
                      -- or they are not
                      Branch (And [NonInlinableSymbolNotEq y x]) e'
                    ]
              | isEq eq,
                isStuckBuiltin x,
                isStuckBuiltin y ->
                pure $
                  Just
                    [ -- either they are equal
                      Branch (And [NonInlinableSymbolEq x y]) t',
                      -- or they are not
                      Branch (And [NonInlinableSymbolNotEq x y]) e'
                    ]
            _
              | Just v <- termIsMeta c ->
                pure $
                  Just
                    [ -- c is True => t is executed
                      Branch (And [Assign v BTrue]) t',
                      -- c is False => e is executed
                      Branch (And [Assign v BFalse]) e'
                    ]
            _ -> pure Nothing
  branchesBuiltinTerm _ _ _ = pure Nothing
