{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Simple parser for a simple language aimed at helping us
-- writing terms for testing pirouette a with a little less work.
-- A lot of the syntactical choices have been made to make parsing
-- as easy as possible. A program in this language is a set of
-- definitions containing one definition named @main@.
-- One example program would be:
--
-- > -- Declares a datatype with a destructor named match_Maybe
-- > data Maybe (a : Type)
-- >   = Nothing : Maybe a
-- >   | Just : a -> Maybe a
-- >
-- > fun id : all k : Type . k -> k
-- >   = /\k : Type . \x : k . k
-- >
-- > fun cons : all (a : Type) (b : Type) . a -> b -> a
-- >   = /\ (a : Type) (b : Type) . \(x : a) (y : b) . x
-- >
-- > fun main : Integer
-- >   -- type applications are made just like Haskell, so are comments.
-- >   -- The language has Integers and booleans
-- >   = id @Integer (if True then 42 else 0)
module Language.Pirouette.Example.Syntax where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Data
import Data.Foldable
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

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
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

instance Pretty ExType where
  prettyPrec _ TyInteger = "Integer"
  prettyPrec _ TyBool = "Bool"

data ExTerm
  = TermAdd
  | TermSub
  | TermLt
  | TermEq
  | TermIte
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

instance Pretty ExTerm where
  prettyPrec _ TermAdd = "add"
  prettyPrec _ TermSub = "sub"
  prettyPrec _ TermLt = "<"
  prettyPrec _ TermEq = "=="
  prettyPrec _ TermIte = "ite"

data ExConstant
  = ConstInt Integer
  | ConstBool Bool
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

instance Pretty ExConstant where
  prettyPrec _ (ConstInt n) = pretty n
  prettyPrec _ (ConstBool b) = pretty b


-- | The language builtins definition
data Ex deriving (Data)

instance LanguageBuiltins Ex where
  type BuiltinTypes Ex = ExType
  type BuiltinTerms Ex = ExTerm
  type Constants Ex = ExConstant

-- ** Syntactical Categories

data DataDecl = DataDecl [(String, SystF.Kind)] [(String, Ty)]
  deriving (Show)

data FunDecl = FunDecl Ty Expr
  deriving (Show)

data Ty
  = TyLam String SystF.Kind Ty
  | TyAll String SystF.Kind Ty
  | TyFun Ty Ty
  | TyApp Ty Ty
  | TyVar String
  | TyFree String
  | TyBase ExType
  deriving (Show)

data Expr
  = ExprApp Expr Expr
  | ExprTy Ty
  | ExprLam String Ty Expr
  | ExprAbs String SystF.Kind Expr
  | ExprVar String
  | ExprLit ExConstant
  | ExprBase ExTerm
  | ExprIf Expr Expr Expr
  deriving (Show)

-- * Parsers

type Parser = Parsec Void String

-- | Parses a program, consisting in a map of declarations and one distinguished
--  function called main.
parseProgram :: Parser (M.Map String (Either DataDecl FunDecl), FunDecl)
parseProgram = do
  decls <- M.fromList <$> many parseDecl
  case M.lookup "main" decls of
    Just (Right fun) -> return (M.delete "main" decls, fun)
    _ -> error "Main is not present or is not a function definition"

parseDecl :: Parser (String, Either DataDecl FunDecl)
parseDecl =
  (second Left <$> parseDataDecl)
    <|> (second Right <$> parseFunDecl)

-- | Parses a simple datatype declaration:
--
--  > data List (a : Type)
--  >   = Nil : List a
--  >   | Cons : a -> List a -> List a
parseDataDecl :: Parser (String, DataDecl)
parseDataDecl = label "Data declaration" $ do
  try (symbol "data")
  i <- typeName
  vars <- many (parens $ (,) <$> ident <*> (parseTyOf >> parseKind))
  cons <-
    (try (symbol "=") >> ((,) <$> typeName <*> (parseTyOf >> parseType)) `sepBy1` symbol "|")
      <|> return []
  return (i, DataDecl vars cons)

-- | Parses functon declarations:
--
--  > fun suc : Integer -> Integer = \x : Integer -> x + 1
parseFunDecl :: Parser (String, FunDecl)
parseFunDecl = label "Function declaration" $ do
  try (symbol "fun")
  i <- ident
  parseTyOf
  t <- parseType
  symbol "="
  x <- parseTerm
  return (i, FunDecl t x)

parseKind :: Parser SystF.Kind
parseKind =
  label "Kind" $
    makeExprParser
      (parens parseKind <|> (SystF.KStar <$ symbol "Type"))
      [[InfixR $ SystF.KTo <$ symbol "->"]]

parseExType :: Parser ExType
parseExType =
  label "Builtin type" $
    (TyInteger <$ symbol "Integer")
      <|> (TyBool <$ symbol "Bool")

parens :: Parser a -> Parser a
parens a = try (symbol "(") *> a <* symbol ")"

parseType :: Parser Ty
parseType = label "Type" $ makeExprParser pAtom [[InfixL pApp], [InfixR pFun]]
  where
    pApp :: Parser (Ty -> Ty -> Ty)
    pApp = return TyApp

    pFun :: Parser (Ty -> Ty -> Ty)
    pFun = TyFun <$ symbol "->"

    pAll :: Parser Ty
    pAll = label "pAll" $ do
      try (symbol "all")
      parseBinder TyAll (parseBinderNames ident (parseTyOf >> parseKind)) (symbol "." >> parseType)

    pLam :: Parser Ty
    pLam = label "pLam" $ do
      try (symbol "\\")
      parseBinder TyLam (parseBinderNames ident (parseTyOf >> parseKind)) (symbol "." >> parseType)

    pAtom = try $
      asum
        [ pLam,
          pAll,
          parseTypeAtom
        ]

parseTypeAtom :: Parser Ty
parseTypeAtom =
  label "Type atom" $
    asum
      [ TyVar <$> try ident,
        TyBase <$> try parseExType,
        TyFree <$> try typeName,
        parens parseType
      ]

parseExConstants :: Parser ExConstant
parseExConstants =
  label "Constant" $
    asum
      [ ConstInt <$> integer,
        ConstBool <$> parseBoolean
      ]
  where
    parseBoolean = (True <$ symbol "True") <|> (False <$ symbol "False")
    integer :: Parser Integer
    integer = L.lexeme spaceConsumer L.decimal

exprBinApp :: ExTerm -> Expr -> Expr -> Expr
exprBinApp f x = ExprApp (ExprApp (ExprBase f) x)

parseTerm :: Parser Expr
parseTerm = label "Term" $ makeExprParser pAtom ops
  where
    ops =
      [ [InfixL (return ExprApp)],
        [ InfixR (symbol "+" >> return (exprBinApp TermAdd)),
          InfixR (symbol "-" >> return (exprBinApp TermSub))
        ],
        [ InfixN (symbol "<" >> return (exprBinApp TermLt)),
          InfixN (symbol "==" >> return (exprBinApp TermEq))
        ]
      ]

    pAbs :: Parser Expr
    pAbs = do
      try (symbol "/\\")
      parseBinder ExprAbs (parseBinderNames ident (parseTyOf >> parseKind)) (symbol "." >> parseTerm)

    pLam :: Parser Expr
    pLam = do
      try (symbol "\\")
      parseBinder ExprLam (parseBinderNames ident (parseTyOf >> parseType)) (symbol "." >> parseTerm)

    parseIf :: Parser Expr
    parseIf = do
      try (symbol "if")
      c <- parseTerm
      symbol "then"
      t <- parseTerm
      symbol "else"
      ExprIf c t <$> parseTerm

    pAtom :: Parser Expr
    pAtom =
      asum
        [ pAbs,
          pLam,
          parens parseTerm,
          parseIf,
          ExprTy <$> (try (symbol "@") >> parseTypeAtom),
          ExprVar <$> try (ident <|> typeName),
          ExprLit <$> try parseExConstants
        ]

parseTyOf :: Parser ()
parseTyOf = symbol ":"

parseBinderNames :: Parser n -> Parser k -> Parser [(n, k)]
parseBinderNames pN pK =
  some (parens parseOneBinder)
    <|> ((: []) <$> parseOneBinder)
  where
    parseOneBinder = (,) <$> pN <*> pK

parseBinder :: (n -> k -> b -> b) -> Parser [(n, k)] -> Parser b -> Parser b
parseBinder binder parseVars parseBody = do
  vars <- parseVars
  guard (not $ null vars)
  b <- parseBody
  let (n0, k0) : rest = reverse vars
  return $ foldr (\(n, k) b' -> binder n k b') (binder n0 k0 b) rest

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "--") empty

symbol :: String -> Parser ()
symbol = void . L.symbol spaceConsumer

ident :: Parser String
ident = label "identifier" $ do
  i <- lexeme ((:) <$> lowerChar <*> many (alphaNumChar <|> char '_'))
  guard (i `S.notMember` reservedNames)
  return i
  where
    reservedNames :: S.Set String
    reservedNames = S.fromList ["abs", "all", "data", "if", "then", "else", "fun"]

typeName :: Parser String
typeName = label "type-identifier" $ do
  t <- lexeme ((:) <$> upperChar <*> many (alphaNumChar <|> char '_'))
  guard (t `S.notMember` reservedTypeNames)
  return t
  where
    reservedTypeNames :: S.Set String
    reservedTypeNames = S.fromList ["Integer", "Bool", "Type"]
