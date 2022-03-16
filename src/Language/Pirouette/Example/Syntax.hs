
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveLift #-}

module Language.Pirouette.Example.Syntax where

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
import Language.Haskell.TH.Syntax (Lift)

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
  x <- parseTerm
  return (i, FunDecl t x)

parseKind :: Parser SystF.Kind
parseKind =
  makeExprParser
    (parens parseKind <|> (SystF.KStar <$ symbol "Type"))
    [[InfixR $ SystF.KTo <$ symbol "->" ]]

data ExTypes
  = TyInteger
  | TyBool
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

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

    pAtom = asum
      [ pLamAll (try (symbol "all") >> return TyAll)
      , pLamAll (symbol "\\" >> return TyLam)
      , parseTypeAtom
      ]

parseTypeAtom :: Parser Ty
parseTypeAtom = asum
   [ TyVar <$> try ident
   , TyBase <$> try parseExType
   , TyFree <$> try typeName
   , parens parseType
   ]


data ExTerm
  = TermAdd
  | TermSub
  | TermLt
  | TermEq
  | TermIte
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

data ExConstant
  = ConstInt Integer
  | ConstBool Bool
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

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

parseTerm :: Parser Expr
parseTerm = makeExprParser pAtom ops
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
        >> ExprAbs <$> ident <*> (symbol "::" >> parseKind) <*> (symbol "." >> parseTerm)

    pLam :: Parser Expr
    pLam = try (symbol "\\")
        >> ExprLam <$> ident <*> (symbol "::" >> parseType) <*> (symbol "." >> parseTerm)

    parseIf :: Parser Expr
    parseIf = do
      try (symbol "if")
      c <- parseTerm
      symbol "then"
      t <- parseTerm
      symbol "else"
      ExprIf c t <$> parseTerm

    pAtom :: Parser Expr
    pAtom = asum
      [ pAbs
      , pLam
      , parens parseTerm
      , parseIf
      , ExprTy <$> (try (symbol "@") >> parseTypeAtom)
      , ExprVar <$> try ident
      , ExprLit <$> try parseExConstants
      ]

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "--") empty

symbol :: String -> Parser ()
symbol = void . L.symbol spaceConsumer

ident :: Parser String
ident = do
  i <- lexeme ((:) <$> lowerChar <*> many (alphaNumChar <|> char '_'))
  guard (i `S.notMember` reservedNames)
  return i
  where
    reservedNames :: S.Set String
    reservedNames = S.fromList ["abs", "all", "data", "if", "then", "else", "fun"]

typeName :: Parser String
typeName = do
  t <- lexeme ((:) <$> upperChar <*> many (alphaNumChar <|> char '_'))
  guard (t `S.notMember` reservedTypeNames)
  return t
  where
    reservedTypeNames :: S.Set String
    reservedTypeNames = S.fromList ["Integer", "Bool", "Type"]
