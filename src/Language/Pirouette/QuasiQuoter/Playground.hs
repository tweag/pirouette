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
pProg = Prog <$> many pDecl <* P.eof

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

go :: String -> IO ()
go input = case evalState (P.runParserT pProg "input" input) [] of
  Left err -> putStrLn (P.errorBundlePretty err)
  Right prog -> print prog

-- TODO Comment a clear example of why we cannot get with it with a list of pos
-- only
-- let x =
--    let y = let z = let a =


-- Bla blu toy language

data Bla = Bla [Blu] deriving Show
data Blu = Blu [Blo] deriving (Show)
data Blo = Blo deriving (Show)

pBlo :: Parser Blo
pBlo = P.label "Blo" $ Blo <$ symbol "blo"

pBla :: Parser Bla
pBla = P.label "Bla" $ do
  symbol "bla"
  blus <- many pBlu -- TODO Introduce linefold here
  return (Bla blus)

pBlu :: Parser Blu
pBlu = P.label "Blu" $ do
  symbol "blu"
  blos <- many pBlo
  return (Blu blos)

pBlas :: Parser [Bla]
pBlas = many (lineFold pBla) <* P.eof

bla0 :: String -- Should fail
bla0 = "blablu"

bla1 :: String
bla1 = "bla blu blu blu"

bla2 :: String
bla2 = "bla\n\
       \  blu\n\
       \  blu\n\
       \  blu"

bla3 :: String -- Fails as expected
bla3 = "bla\n\
       \  blu\n\
       \  blu\n\
       \ blu"

bla4 :: String
bla4 = "bla\n\
       \  blu blu\n\
       \  blu\n"

bla5 :: String
bla5 = "bla\n\
       \  blu\n\
       \       blu\n\
       \    blu\n\
       \     blu"

bla6 :: String
bla6 = "bla blu\n\
       \  blu\n\
       \  blu\n\
       \bla blu"

-- Should fail but succeeds
-- We would like to specify that bla must begin a line
bla7 :: String
bla7 = "bla blu bla\n\
       \bla"

bla8 :: String
bla8 = "bla blu blo blo blu"

bla9 :: String
bla9 = "bla\n\
        \    blu blo\n\
        \        blo\n\
        \    blu"

-- Should succeed but fails
bla10 :: String
bla10 = "bla blu blo\n\
       \         blo\n\
       \     blu"


go2 :: String -> IO ()
go2 input = case evalState (P.runParserT pBlas "input" input) [] of
  Left err -> putStrLn (P.errorBundlePretty err)
  Right prog -> print prog
