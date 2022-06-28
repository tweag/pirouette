{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

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
module Language.Pirouette.QuasiQuoter.Syntax where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Foldable
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Utils (monoNameSep)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- ** Class for parsing language builtins

type Parser = Parsec Void String

-- | Auxiliary constraint for lifting terms of a given language.
type LanguageLift lang =
  ( Lift (BuiltinTypes lang),
    Lift (BuiltinTerms lang),
    Lift (Constants lang)
  )

-- | Groups all the necessary bits to have a working quasi-quoter for a given language.
-- To see an example instance, check "Language.Pirouette.Example.Syntax".
class (LanguageLift lang, LanguageBuiltins lang) => LanguageParser lang where
  parseBuiltinTerm :: Parser (BuiltinTerms lang)

  -- | Augments the expression parser operator table
  operators :: [[Operator Parser (Expr lang)]]

  parseBuiltinType :: Parser (BuiltinTypes lang)
  parseConstant :: Parser (Constants lang)

  -- | Set of term names that are reserved; often include any builtin constructor names
  reservedNames :: S.Set String

  -- | Set of type names that are reserved; often include the builtin types
  reservedTypeNames :: S.Set String

  -- This next 'ifThenElse' function is here due to a technicality in 'Language.Pirouette.QuasiQuoter.ToTerm.trTerm';
  -- because we have dedicated syntax for if-statements, we need a way of translating them into
  -- Pirouette's base language, that has no such thing. This is technically not a parser, but I think
  -- it's better than creating a separate type class for it.

  -- | How to represent if-then-else. Different languages might have different builtins for that.
  ifThenElse :: Type lang -> Term lang -> Term lang -> Term lang -> Term lang

-- ** Syntactical Categories

data DataDecl lang = DataDecl [(String, SystF.Kind)] [(String, Ty lang)]

deriving instance (Show (BuiltinTypes lang)) => Show (DataDecl lang)

data FunDecl lang = FunDecl Rec (Ty lang) (Expr lang)

deriving instance
  (Show (BuiltinTypes lang), Show (BuiltinTerms lang), Show (Constants lang)) =>
  Show (FunDecl lang)

data Ty lang
  = TyLam String SystF.Kind (Ty lang)
  | TyAll String SystF.Kind (Ty lang)
  | TyFun (Ty lang) (Ty lang)
  | TyApp (Ty lang) (Ty lang)
  | TyVar String
  | TyFree String
  | TyBase (BuiltinTypes lang)

deriving instance (Show (BuiltinTypes lang)) => Show (Ty lang)

data Expr lang
  = ExprApp (Expr lang) (Expr lang)
  | ExprTy (Ty lang)
  | ExprLam String (Ty lang) (Expr lang)
  | ExprAbs String SystF.Kind (Expr lang)
  | ExprVar String
  | ExprLit (Constants lang)
  | ExprBase (BuiltinTerms lang)
  | ExprIf (Ty lang) (Expr lang) (Expr lang) (Expr lang)

deriving instance
  (Show (BuiltinTypes lang), Show (BuiltinTerms lang), Show (Constants lang)) =>
  Show (Expr lang)

-- * Parsers

-- | Parses a program, consisting in a map of declarations and one distinguished
--  function called main.
parseProgram ::
  (LanguageParser lang) =>
  Parser (M.Map String (Either (DataDecl lang) (FunDecl lang)), FunDecl lang)
parseProgram = do
  decls <- M.fromList <$> many parseDecl
  case M.lookup "main" decls of
    Just (Right fun) -> return (M.delete "main" decls, fun)
    _ -> error "Main is not present or is not a function definition"

parseDecl :: (LanguageParser lang) => Parser (String, Either (DataDecl lang) (FunDecl lang))
parseDecl =
  (second Left <$> parseDataDecl)
    <|> (second Right <$> parseFunDecl)

-- | Parses a simple datatype declaration:
--
--  > data List (a : Type)
--  >   = Nil : List a
--  >   | Cons : a -> List a -> List a
parseDataDecl :: forall lang. (LanguageParser lang) => Parser (String, DataDecl lang)
parseDataDecl = label "Data declaration" $ do
  try (symbol "data")
  i <- typeName @lang
  vars <- many (parens $ (,) <$> ident @lang <*> (parseTyOf >> parseKind))
  cons <-
    (try (symbol "=") >> ((,) <$> typeName @lang <*> (parseTyOf >> parseType)) `sepBy1` symbol "|")
      <|> return []
  return (i, DataDecl vars cons)

-- | Parses functon declarations:
--
--  > fun suc : Integer -> Integer = \x : Integer -> x + 1
parseFunDecl :: forall lang. (LanguageParser lang) => Parser (String, FunDecl lang)
parseFunDecl = label "Function declaration" $ do
  try (symbol "fun")
  r <- NonRec <$ symbol "nonrec" <|> pure Rec
  i <- ident @lang
  parseTyOf
  t <- parseType
  symbol "="
  x <- parseTerm
  return (i, FunDecl r t x)

parseKind :: Parser SystF.Kind
parseKind =
  label "Kind" $
    makeExprParser
      (parens parseKind <|> (SystF.KStar <$ symbol "Type"))
      [[InfixR $ SystF.KTo <$ symbol "->"]]

parens :: Parser a -> Parser a
parens a = try (symbol "(") *> a <* symbol ")"

parseType :: forall lang. (LanguageParser lang) => Parser (Ty lang)
parseType = label "Type" $ makeExprParser pAtom [[InfixL pApp], [InfixR pFun]]
  where
    pApp :: Parser (Ty lang -> Ty lang -> Ty lang)
    pApp = return TyApp

    pFun :: Parser (Ty lang -> Ty lang -> Ty lang)
    pFun = TyFun <$ symbol "->"

    pAll :: Parser (Ty lang)
    pAll = label "pAll" $ do
      try (symbol "all")
      parseBinder TyAll (parseBinderNames (ident @lang) (parseTyOf >> parseKind)) (symbol "." >> parseType)

    pLam :: Parser (Ty lang)
    pLam = label "pLam" $ do
      try (symbol "\\")
      parseBinder TyLam (parseBinderNames (ident @lang) (parseTyOf >> parseKind)) (symbol "." >> parseType)

    pAtom =
      try $
        asum
          [ pLam,
            pAll,
            parseTypeAtom
          ]

parseTypeAtom :: forall lang. (LanguageParser lang) => Parser (Ty lang)
parseTypeAtom =
  label "Type atom" $
    asum
      [ TyVar <$> try (ident @lang),
        TyBase <$> try (parseBuiltinType @lang),
        TyFree <$> try (typeName @lang),
        parens parseType
      ]

exprBinApp :: BuiltinTerms lang -> Expr lang -> Expr lang -> Expr lang
exprBinApp f x = ExprApp (ExprApp (ExprBase f) x)

parseTerm :: forall lang. (LanguageParser lang) => Parser (Expr lang)
parseTerm = label "Term" $ makeExprParser pAtom ops
  where
    ops =
      [InfixL (return ExprApp)] :
      operators @lang

    pAbs :: Parser (Expr lang)
    pAbs = do
      try (symbol "/\\")
      parseBinder ExprAbs (parseBinderNames (ident @lang) (parseTyOf >> parseKind)) (symbol "." >> parseTerm)

    pLam :: Parser (Expr lang)
    pLam = do
      try (symbol "\\")
      parseBinder ExprLam (parseBinderNames (ident @lang) (parseTyOf >> parseType)) (symbol "." >> parseTerm)

    parseIf :: Parser (Expr lang)
    parseIf = do
      try (symbol "if")
      ty <- symbol "@" >> parseTypeAtom
      c <- parseTerm
      symbol "then"
      t <- parseTerm
      symbol "else"
      ExprIf ty c t <$> parseTerm

    pAtom :: Parser (Expr lang)
    pAtom =
      asum
        [ pAbs,
          pLam,
          parens parseTerm,
          parseIf,
          ExprBase <$> try (parseBuiltinTerm @lang),
          ExprTy <$> (try (symbol "@") >> parseTypeAtom),
          ExprLit <$> try (parseConstant @lang),
          ExprVar <$> try (ident @lang <|> typeName @lang)
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
  return $ foldr (uncurry binder) b vars

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "--") empty

symbol :: String -> Parser ()
symbol = void . L.symbol spaceConsumer

ident :: forall lang. (LanguageParser lang) => Parser String
ident = label "identifier" $ do
  i <- lexeme ((:) <$> (lowerChar <|> char '_') <*> restOfName)
  guard (i `S.notMember` reserved)
  return i
  where
    reserved :: S.Set String
    reserved =
      S.fromList ["abs", "all", "data", "if", "then", "else", "fun"]
        `S.union` reservedNames @lang

typeName :: forall lang. (LanguageParser lang) => Parser String
typeName = label "type-identifier" $ do
  t <- lexeme ((:) <$> upperChar <*> restOfName)
  guard (t `S.notMember` reservedTypeNames @lang)
  return t

-- where
--   reservedTypeNames :: S.Set String
--   reservedTypeNames =

restOfName :: Parser String
restOfName = many (alphaNumChar <|> char '_' <|> char monoNameSep)
