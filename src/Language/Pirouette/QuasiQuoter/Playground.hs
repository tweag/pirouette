{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Pirouette.QuasiQuoter.Playground where

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Combinators.Expr as Expr
import Control.Monad.State
import Data.Void
import Data.Set
import qualified Data.Set as Set
import Text.Megaparsec (ParsecT)
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as L
import Debug.Trace
import GHC.Num.BigNat (bigNatFromWordListUnsafe)

-- ** Class for parsing language builtins

-- type Parser = Parsec Void String

type IndentLevel = Int

-- data LineFoldSt
--   = NoLineFold
--   | LineFoldStart
--   | LineFold P.Pos

data LineFoldSt
  = LineFoldStart
  | LineFold P.Pos
  deriving Show

type Parser = ParsecT Void String (State [LineFoldSt])

data Op
  = OpPlus
  | OpMinus
  deriving (Show)

data Expr
  = ExprVar String
  | ExprApp Expr Expr
  | ExprOp Op Expr Expr
  | ExprLet [Decl] Expr
  deriving (Show)

data Decl = Decl String Expr
  deriving (Show)

newtype Prog = Prog [Decl]
  deriving (Show)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer'

spaceConsumer :: Parser ()
spaceConsumer = L.space P.space1 P.empty P.empty

-- TODO Get rid of blank lines in line folds if any
spaceConsumer' :: Parser ()
spaceConsumer' =
  get >>= \case
    [] -> spaceConsumer
    LineFoldStart : fs -> do
      _ <- P.hspace
      P.try
        ( do
            _ <- P.newline
            _ <- P.hspace
            P.SourcePos _ _ currentCol <- P.getSourcePos
            if currentCol > previousIndentCol fs
              then void (put (LineFold currentCol : fs))
              else fail "not indented enough"
            return ()
        )
        <|> return ()
    LineFold indentCol : _ -> do
      _ <- P.hspace
      P.try
        ( do
            _ <- P.newline
            _ <- P.hspace
            P.SourcePos _ _ currentCol <- P.getSourcePos
            if currentCol >= indentCol
              then return ()
              else fail "not indented enough"
        )
        <|> return ()
  where
    previousIndentCol :: [LineFoldSt] -> P.Pos
    previousIndentCol [] = P.mkPos 1
    previousIndentCol (LineFoldStart : fs) = previousIndentCol fs
    previousIndentCol (LineFold col : _) = col

symbol :: String -> Parser ()
symbol = void . L.symbol spaceConsumer'

parens :: Parser a -> Parser a
parens x = P.try (symbol "(") *> x <* symbol ")"

reservedNames :: Set String
reservedNames = fromList ["let", "in"]

ident :: Parser String
ident = P.try $ do
  i <- lexeme (some P.alphaNumChar)
  if Set.member i reservedNames
     then fail "reserved name"
     else return i

pExpr :: Parser Expr
pExpr =
  P.label "Expr" $
    P.try (
      do
        symbol "let"
        decl <- some pDecl
        symbol "in"
        ExprLet decl <$> pExpr
          )
          <|>
    Expr.makeExprParser
      (parens pExpr <|> (ExprVar <$> ident))
      [ [Expr.InfixR $ ExprOp OpPlus <$ symbol "+"],
        [Expr.InfixR $ ExprOp OpMinus <$ symbol "-"],
        [Expr.InfixL $ return ExprApp]
      ]

lineFold :: Parser a -> Parser a
lineFold p = do
  modify (LineFoldStart :)
  res <- p
  modify tail
  spaceConsumer'
  return res

traceLineFold :: Parser ()
traceLineFold = get >>= \s -> traceM (show s)

pDecl :: Parser Decl
pDecl = P.label "Declaration" $ do
  traceLineFold
  Decl
    <$> ident <* symbol "="
    <*> lineFold pExpr

pProg :: Parser Prog
pProg = Prog <$> many pDecl <* P.atEnd

input1 :: String
input1 = "a = foo + bar - (baz + x) + y\n"

input2 :: String
input2 =
  "bla = blu bla =\n\
  \blu"

input3 :: String
input3 =
  "a = f foo\n\
  \  + bar x y\n\
  \  - (baz\n\
  \     x\n\
  \     y\n\
  \     foo) + y\n\
  \b = hello"

input4 :: String
input4 =
  "a = f foo\n\
  \  + bar x y\n\
  \  - (baz\n\
  \     x\n\
  \     y\n\
  \     foo) + y\n\
  \b = hello\n\
  \c = foo\n\
  \           bar\n\
  \           baz"

input5 :: String
input5 =
  "a = f (let x = foo in bar foo)"

input6 :: String
input6 =
  "a = f\n\
  \    (let x = foo\n\
  \         y = foo\n\
  \    in bar)"

-- TODO Comment a clear example of why we cannot get with it with a list of pos
-- only
-- let x =
--    let y = let z = let a =

-- many $ lineFold (symbol "bla" >> lineFold (some (symbol "blu")))
--
-- bla blu blu blu 
--
-- bla 
--  blu blu blu
--
-- bla 
--  blu
--  blu
--  blu
--
-- bla 
--    blu
--    blu
--   blu
--
-- bla
--  blu blu
--  blu
--
-- bla
--  blu
--     blu
--   blu
--    blu
--
-- SHOULD NOT PARSE
-- bla blu bla
-- bla
--
-- TODO Use that toy language to develop and debug lineFolds

go :: String -> IO ()
go input = case evalState (P.runParserT pProg "input" input) [] of
  Left err -> putStrLn (P.errorBundlePretty err)
  Right prog -> print prog
