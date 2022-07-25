{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Pirouette.QuasiQuoter.Playground where

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Combinators.Expr as Expr
import Control.Monad.Reader
import Data.Void
import Text.Megaparsec (ParsecT)
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as L

-- ** Class for parsing language builtins

-- type Parser = Parsec Void String

type IndentLevel = Int

type Parser = ParsecT Void String (Reader IndentLevel)

data Op
  = OpPlus
  | OpMinus
  deriving (Show)

data Expr
  = ExprVar String
  | ExprApp Expr Expr
  | ExprOp Op Expr Expr
  deriving (Show)

data Decl = Decl String Expr
  deriving (Show)

newtype Prog = Prog [Decl]
  deriving (Show)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer'

spaceConsumer :: Parser ()
spaceConsumer = L.space P.space1 P.empty P.empty

spaceConsumer' :: Parser ()
spaceConsumer' = do
  _ <- P.hspace
  _ <- 
    P.try (do
      _ <- P.newline
      _ <- P.hspace
      currentIndentLevel <- ask
      P.SourcePos _ _ col <- P.getSourcePos
      if P.unPos col >= currentIndentLevel
        then return ()
        else fail "not indented enough") <|> return ()
  return ()

-- spaceConsumer' :: Parser ()
-- spaceConsumer' = do
--   _ <- P.hspace
--   _ <- 
--     P.try (do
--       _ <- P.newline
--       currentIndentLevel <- ask
--       (tokens, _) <- P.match P.hspace
--       if length tokens >= currentIndentLevel
--         then return ()
--         else fail "not indented enough") <|> return ()
--   return ()

symbol :: String -> Parser ()
symbol = void . L.symbol spaceConsumer'

parens :: Parser a -> Parser a
parens x = P.try (symbol "(") *> x <* symbol ")"

ident :: Parser String
ident = lexeme (some P.alphaNumChar)

pExpr :: Parser Expr
pExpr =
  P.label "Expr" $
    Expr.makeExprParser
      (parens pExpr <|> (ExprVar <$> ident))
      [ [Expr.InfixR $ ExprOp OpPlus <$ symbol "+"],
        [Expr.InfixR $ ExprOp OpMinus <$ symbol "-"],
        [Expr.InfixL $ return ExprApp]
      ]

indented :: (Int -> Int) -> Parser a -> Parser a
indented f p = local f p <* spaceConsumer

pDecl :: Parser Decl
pDecl =
  Decl
    <$> ident <* symbol "="
    <*> indented (+ 1) pExpr

pProg :: Parser Prog
pProg = Prog <$> many pDecl <* P.atEnd

input1 :: String
input1 = "a = foo + bar - (baz + x) + y\n"

input2 :: String
input2 =
  "a = f foo\n\
  \  + bar x y\n\
  \  - (baz\n\
  \     x\n\
  \     y\n\
  \     foo) + y"

input3 :: String
input3 =
  "a = f foo\n\
  \  + bar x y\n\
  \  - (baz\n\
  \     x\n\
  \     y\n\
  \     foo) + y\n\
  \b = hello"

go :: String -> IO ()
go input = case runReader (P.runParserT pProg "input" input) 1 of
  Left err -> putStrLn (P.errorBundlePretty err)
  Right prog -> print prog
