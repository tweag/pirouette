
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
module Pirouette.Languages.Example.Syntax where


import qualified Data.Text as T
import Text.Megaparsec
import Data.Void
import Data.Data
import qualified Data.Map as M
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Char
import Control.Monad
import Control.Monad.Combinators.Expr
import qualified Pirouette.Term.Syntax.SystemF as SystF
import qualified Data.Set as S
import Data.Foldable
import Control.Arrow (second)

type Parser = Parsec Void String

parseProgram :: Parser (M.Map String (Either DataDecl FunDecl), FunDecl)
parseProgram = do
  decls <- M.fromList <$> many parseDecl
  case M.lookup "main" decls of
    Just (Right fun) -> return (M.delete "main" decls, fun)
    _ -> error "Main is not present or is not a function definition"

parseDecl :: Parser (String, Either DataDecl FunDecl)
parseDecl = (second Left <$> parseDataDecl)
        <|> (second Right <$> parseFunDecl)

data DataDecl = DataDecl [(String, SystF.Kind)] [(String, Ty)]
  deriving (Show)

-- |Parses a simple datatype declaration:
--
-- > data List (a :: Type)
-- >   = Nil :: List a
-- >   | Cons :: a -> List a -> List a
--
parseDataDecl :: Parser (String, DataDecl)
parseDataDecl = do
  try (symbol "data")
  i <- typeName
  vars <- many (parens $ (,) <$> ident <*> (symbol "::" >> parseKind))
  cons <- (try (symbol "=") >> ((,) <$> typeName <*> (symbol "::" >> parseType)) `sepBy1` symbol "|")
         <|> return []
  return (i, DataDecl vars cons)

data FunDecl = FunDecl Ty Expr
  deriving (Show)

parseFunDecl :: Parser (String, FunDecl)
parseFunDecl = do
  try (symbol "fun")
  i <- ident
  symbol "::"
  t <- parseType
  symbol "="
  x <- parseExpr
  return (i, FunDecl t x)

parseKind :: Parser SystF.Kind
parseKind =
  makeExprParser
    (parens parseKind <|> (SystF.KStar <$ symbol "Type"))
    [[InfixR $ SystF.KTo <$ symbol "->" ]]

data ExTypes
  = TyInteger
  | TyBool
  deriving (Eq, Ord, Show, Data, Typeable)

parseExType :: Parser ExTypes
parseExType = (TyInteger <$ symbol "Integer")
          <|> (TyBool <$ symbol "Bool")

data Ty
  = TyLam String SystF.Kind Ty
  | TyAll String SystF.Kind Ty
  | TyFun Ty Ty
  | TyApp Ty Ty
  | TyVar String
  | TyFree String
  | TyBase ExTypes
  deriving (Show)

parens :: Parser a -> Parser a
parens a = try (symbol "(") *> a <* symbol ")"

parseType :: Parser Ty
parseType = makeExprParser pAtom [ [ InfixL pApp ] , [ InfixR pFun ] ]
  where
    pAtom :: Parser Ty
    pAtom = asum
       [ pLamAll (try (symbol "all") >> return TyAll)
       , pLamAll (symbol "\\" >> return TyLam)
       , TyVar <$> try ident
       , TyBase <$> try parseExType
       , TyFree <$> try typeName
       , parens parseType
       ]

    pApp :: Parser (Ty -> Ty -> Ty)
    pApp = return TyApp

    pFun :: Parser (Ty -> Ty -> Ty)
    pFun = TyFun <$ symbol "->"

    pLamAll :: Parser (String -> SystF.Kind -> Ty -> Ty) -> Parser Ty
    pLamAll sym = do
      f <- try sym
      f <$> ident
        <*> (symbol "::" >> parseKind)
        <*> (symbol "." >> parseType)

data ExTerm
  = TermAdd
  | TermSub
  | TermLt
  | TermEq
  deriving (Eq, Ord, Show, Data, Typeable)

parseExTerm :: Parser ExTerm
parseExTerm = asum
  [ TermAdd <$ symbol "+"
  , TermSub <$ symbol "-"
  , TermLt <$ symbol "<"
  , TermEq <$ symbol "=="
  ]

data ExConstant
  = ConstInt Integer
  | ConstBool Bool
  deriving (Eq, Ord, Show, Data, Typeable)

parseExConstants :: Parser ExConstant
parseExConstants = asum
  [ ConstInt <$> integer
  , ConstBool <$> parseBoolean
  ]
  where
    parseBoolean = (True <$ symbol "True") <|> (False <$ symbol "False")
    integer :: Parser Integer
    integer = L.lexeme spaceConsumer L.decimal

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

exprBinApp :: Expr -> Expr -> Expr -> Expr
exprBinApp f x = ExprApp (ExprApp f x)

exprBinApp' :: ExTerm -> Expr -> Expr -> Expr
exprBinApp' f x = ExprApp (ExprApp (ExprBase f) x)

parseExpr :: Parser Expr
parseExpr = makeExprParser pAtom ops
  where
    ops = [ [ InfixL (return ExprApp) ]
          , [ InfixR (symbol "+" >> return (exprBinApp' TermAdd))
            , InfixR (symbol "-" >> return (exprBinApp' TermSub))
            ]
          , [ InfixN (symbol "<" >> return (exprBinApp' TermLt))
            , InfixN (symbol "==" >> return (exprBinApp' TermEq))
            ]
          ]

    pAbs :: Parser Expr
    pAbs = try (symbol "abs")
        >> ExprAbs <$> ident <*> (symbol "::" >> parseKind) <*> (symbol "." >> parseExpr)

    pLam :: Parser Expr
    pLam = try (symbol "\\")
        >> ExprLam <$> ident <*> (symbol "::" >> parseType) <*> (symbol "." >> parseExpr)

    parseIf :: Parser Expr
    parseIf = do
      try (symbol "if")
      c <- parseExpr
      symbol "then"
      t <- parseExpr
      symbol "else"
      ExprIf c t <$> parseExpr

    pAtom :: Parser Expr
    pAtom = asum
      [ pAbs
      , pLam
      , parens parseExpr
      , ExprTy <$> (try (symbol "@") >> parseType)
      , ExprVar <$> try ident
      , ExprLit <$> try parseExConstants
      ]

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "--") empty

symbol :: String -> Parser ()
symbol = void . L.symbol spaceConsumer

ident :: Parser String
ident = do
  i <- L.lexeme spaceConsumer ((:) <$> lowerChar <*> many alphaNumChar)
  guard (i `S.notMember` reservedNames)
  return i
  where
    reservedNames :: S.Set String
    reservedNames = S.fromList ["abs", "all", "data", "if", "then", "else", "fun"]

typeName :: Parser String
typeName = do
  t <- L.lexeme spaceConsumer ((:) <$> upperChar <*> many alphaNumChar)
  guard (t `S.notMember` reservedTypeNames)
  return t
  where
    reservedTypeNames :: S.Set String
    reservedTypeNames = S.fromList ["Integer", "Bool", "Type"]
