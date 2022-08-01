{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Simple parser for a simple language aimed at helping us
-- writing terms for testing pirouette a with a little less work.
-- A lot of the syntactical choices have been made to make parsing
-- as easy as possible. A program in this language is a set of
-- definitions. One example program would be:
--
-- > -- Declares a datatype with a destructor named match_Maybe
-- > data Maybe (a : *)
-- >   = Nothing : Maybe a
-- >   | Just : a -> Maybe a
-- >
-- > id : forall k . k -> k
-- > id @k x = x
-- >
-- > const : forall (a : *) (b : *) . a -> b -> a
-- > const @a @b x y = x
-- >
-- > val : Integer
-- >   -- type applications are made just like Haskell, so are comments.
-- >   -- The language has Integers and booleans
-- >   = id @Integer (if True then 42 else 0)
module Language.Pirouette.QuasiQuoter.Syntax where

import Control.Applicative
import Control.Arrow (second)
import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.Reader
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set as Set (Set)
import qualified Data.Set as Set
import Data.Void
import Language.Haskell.TH.Syntax (Lift)
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.Monomorphization (monoNameSep)
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as L

-- ** Class for parsing language builtins

-- | State of line folding. There is basic support for line folding at the top
-- level (data and function declarations). The parser is either outside a line
-- folding block ("Nothing") or inside a line folding block which began at a
-- given column "pos" ("Just pos"). There is no support yet for nested line
-- folded sections.
type LineFoldSt = Maybe P.Pos

-- | The parser has an environment to make line folding possible.
type Parser = P.ParsecT Void String (Reader LineFoldSt)

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
  reservedTermNames :: Set String

  -- | Set of type names that are reserved; often include the builtin types
  reservedTypeNames :: Set String

  -- This next 'ifThenElse' function is here due to a technicality in 'Language.Pirouette.QuasiQuoter.ToTerm.trTerm';
  -- because we have dedicated syntax for if-statements, we need a way of translating them into
  -- Pirouette's base language, that has no such thing. This is technically not a parser, but I think
  -- it's better than creating a separate type class for it.

  -- | How to represent if-then-else. Different languages might have different builtins for that.
  ifThenElse :: Type lang -> Term lang -> Term lang -> Term lang -> Term lang

-- ** Syntactical Categories

-- | Algebraic datatype declaration
data DataDecl lang = DataDecl [(String, SystF.Kind)] [(String, Ty lang)] (Maybe String)

deriving instance (Show (BuiltinTypes lang)) => Show (DataDecl lang)

-- | Function declaration
data FunDecl lang = FunDecl Rec (Ty lang) (Expr lang)

deriving instance
  (Show (BuiltinTypes lang), Show (BuiltinTerms lang), Show (Constants lang)) =>
  Show (FunDecl lang)

-- | Type level
data Ty lang
  = TyLam String SystF.Kind (Ty lang)
  | TyAll String SystF.Kind (Ty lang)
  | TyFun (Ty lang) (Ty lang)
  | TyApp (Ty lang) (Ty lang)
  | TyVar String
  | TyFree String
  | TyBase (BuiltinTypes lang)

deriving instance (Show (BuiltinTypes lang)) => Show (Ty lang)

-- | Term level
data Expr lang
  = ExprApp (Expr lang) (Expr lang)
  | ExprTy (Ty lang)
  | ExprLam String (Ty lang) (Expr lang)
  | ExprAbs String SystF.Kind (Expr lang)
  | ExprVar String
  | ExprLit (Constants lang)
  | ExprBase (BuiltinTerms lang)
  | ExprIf (Ty lang) (Expr lang) (Expr lang) (Expr lang)
  | ExprCase (Ty lang) (Ty lang) (Expr lang) [(Pattern lang, Expr lang)]
  | ExprBottom (Ty lang)

-- | Patterns for pattern-matching in case statements and function declaration
data Pattern lang
  = PatternConstr String [Pattern lang]
  | PatternVar String
  | PatternAll

deriving instance
  (Show (BuiltinTypes lang), Show (BuiltinTerms lang), Show (Constants lang)) =>
  Show (Pattern lang)

deriving instance
  (Show (BuiltinTypes lang), Show (BuiltinTerms lang), Show (Constants lang)) =>
  Show (Expr lang)

-- * Parsers

-- | A program is some set of declarations
parseProgram ::
  (LanguageParser lang) =>
  Parser (Map String (Either (DataDecl lang) (FunDecl lang)))
parseProgram = Map.fromList <$> P.many parseDecl

-- | A declaration is either a datatype or a function
parseDecl ::
  (LanguageParser lang) =>
  Parser (String, Either (DataDecl lang) (FunDecl lang))
parseDecl =
  (second Left <$> lineFold parseDataDecl)
    <|> (second Right <$> parseFunDecl)

-- | Parses a simple datatype declaration:
--
--  > data List (a : Type)
--  >   = Nil : List a
--  >   | Cons : a -> List a -> List a
parseDataDecl :: forall lang. (LanguageParser lang) => Parser (String, DataDecl lang)
parseDataDecl = P.label "Data declaration" $ do
  P.try (symbol "data")
  i <- typeName @lang
  vars <- many (parseTypeVarKind @lang)
  cons <-
    (P.try (symbol "=") >> ((,) <$> typeName @lang <*> (parseTyOf >> parseType)) `P.sepBy1` symbol "|")
      <|> return []
  dest <- optional (symbol "destructor" >> P.try (ident @lang) <|> typeName @lang)
  return (i, DataDecl vars cons dest)

-- | Function parameter: either term or type level
--
-- TODO "Ident String" is eventually intended to be replaced by "Pattern lang"
-- to provide syntaxic sugar for pattern matching without using explicit case
-- statements.
-- For now, the lack of proper bug free line folding prevents us from allowing
-- the required multi body functions
data Param = Ident String | TyIdent String deriving (Eq, Show)

-- | Parses functon declarations following the new syntax:
--
--  > fun suc : Integer -> Integer = \x : Integer -> x + 1
parseFunDecl :: forall lang. (LanguageParser lang) => Parser (String, FunDecl lang)
parseFunDecl = P.label "Function declaration (new syntax)" $ do
  (r, funIdent, funType) <- lineFold $ do
    r <- NonRec <$ symbol "nonrec" <|> pure Rec
    funIdent <- ident @lang
    parseTyOf
    funType <- parseType
    return (r, funIdent, funType)
  lineFold $ do
    _ <- symbol funIdent
    -- TODO Fail when there are duplicate names in the term or type worlds
    -- and add a regression test
    params <- many $ (TyIdent <$> (P.char '@' >> ident @lang)) <|> (Ident <$> ident @lang)
    symbol "="
    body <- parseTerm
    -- Uncomment the following for debug info
    -- traceM $ "---- Function \"" <> funIdent <> "\" (" <> show r <> ") ----"
    -- traceM $ "Type: " <> show funType
    -- traceM $ "Parameters: " <> show params
    -- traceM $ "Body: " <> show body
    -- traceM $ "Processed term: " <> show (funTerm funType params body)
    return (funIdent, FunDecl r funType (funTerm funType params body))

-- | Term corresponding to the desugared body declaration using given parameter
-- types and names.
funTerm :: forall lang. Ty lang -> [Param] -> Expr lang -> Expr lang
funTerm (TyAll i k t2) (TyIdent tp : ps) body =
  ExprAbs tp k (funTerm (substTyVarType i tp t2) ps body)
funTerm (TyFun t1 t2) (Ident p : ps) body =
  ExprLam p t1 (funTerm t2 ps body)
funTerm _ [] body = body
funTerm _ _ _ = error "Unexpected parameters in function declaration"

-- | Apply a type variable name substitution taking into account naming
-- collisions by renaming the conficting name beforehand.
-- E.g. In `/\ a : * . /\ b : * . a -> b -> b`, by applying the type to `b`,
-- the result will be: `/\ b_ : * . b -> b_ -> b_`
substTyVarType :: String -> String -> Ty lang -> Ty lang
-- TODO Add test cases involving "TyLam"
substTyVarType i i' (TyLam s ki ty)
  | s == i' =
    -- Naming conflict: append `_` before renaming to avoid conflict
    TyLam
      (s <> "_")
      ki
      (substTyVarType i i' . substTyVarType s (s <> "_") $ ty)
  | otherwise = TyLam s ki (substTyVarType i i' ty)
substTyVarType i i' (TyAll s ki ty)
  | s == i' = TyAll (s <> "_") ki (substTyVarType i i' . substTyVarType s (s <> "_") $ ty)
  | otherwise = TyAll s ki (substTyVarType i i' ty)
substTyVarType i i' (TyFun ty ty') =
  TyFun (substTyVarType i i' ty) (substTyVarType i i' ty')
substTyVarType i i' (TyApp ty ty') =
  TyApp (substTyVarType i i' ty) (substTyVarType i i' ty')
substTyVarType i i' (TyVar s)
  | s == i = TyVar i'
  | otherwise = TyVar s
substTyVarType _ _ ty = ty -- TyFree, TyBase

-- | Parse kinds using the haskell `*` syntax.
-- E.g. `(* -> *) -> (* -> * -> *)`
parseKind :: Parser SystF.Kind
parseKind =
  P.label "Kind" $
    makeExprParser
      (parens parseKind <|> (SystF.KStar <$ symbol "*"))
      [[InfixR $ SystF.KTo <$ symbol "->"]]

-- | EXPERIMENTAL
-- Parse a kind after the `:` operator or default to kind `*` if omitted.
-- For now, omitting the kind is not yet bug free.
--
-- It only works in `forall` constructions with a single type variable.
-- E.g. `forall a . forall b . a -> b -> b`
--
-- TODO Fix
-- It does not work with multiple variables in a common `forall`:
-- E.g. `forall a b . a -> b -> b` does not work.
-- Use either `forall (a : *) (b : *) . a -> b -> b` or `forall a . forall b .
-- a -> b -> b`
--
-- It also does not work yet in datatype declaration:
-- E.g. `data Maybe a = ...` does not work. Use `data Maybe (a : *) = ...`
-- instead.
parseOptKindOf :: Parser SystF.Kind
parseOptKindOf = P.try (parseTyOf *> parseKind) <|> return SystF.KStar

-- | Parse a type. The following features are supported:
--
-- - Application: `Either a b`
-- - Function arrow: `b -> (a -> b) -> c`
-- - Quantification: `forall (a : * -> *) (b : *) . `
-- - Type lambdas: `\\(a : * -> *) (b : *) . `
parseType :: forall lang. (LanguageParser lang) => Parser (Ty lang)
parseType = P.label "Type" $ makeExprParser pAtom [[InfixL pApp], [InfixR pFun]]
  where
    pApp :: Parser (Ty lang -> Ty lang -> Ty lang)
    pApp = return TyApp

    pFun :: Parser (Ty lang -> Ty lang -> Ty lang)
    pFun = TyFun <$ symbol "->"

    pAll :: Parser (Ty lang)
    pAll = P.label "pAll" $ do
      P.try (symbol "forall")
      parseBinder
        TyAll
        (some (parseTypeVarKind @lang))
        (symbol "." >> parseType)

    pLam :: Parser (Ty lang)
    pLam = P.label "pLam" $ do
      P.try (symbol "\\")
      parseBinder
        TyLam
        (some (parseTypeVarKind @lang))
        (symbol "." >> parseType)

    pAtom =
      P.try $
        asum
          [ pLam,
            pAll,
            parseTypeAtom
          ]

-- | Parse type atoms among type variables, builtins, and types declared in the
-- environment
parseTypeAtom :: forall lang. (LanguageParser lang) => Parser (Ty lang)
parseTypeAtom =
  P.label "Type atom" $
    asum
      [ TyVar <$> P.try (ident @lang),
        TyBase <$> P.try (parseBuiltinType @lang),
        TyFree <$> P.try (typeName @lang),
        parens parseType
      ]

-- TODO Keep in this module?
exprBinApp :: BuiltinTerms lang -> Expr lang -> Expr lang -> Expr lang
exprBinApp f x = ExprApp (ExprApp (ExprBase f) x)

-- | Parse an expression. The following features are supported:
--
-- - Type abstraction: `/\ (a : * -> *) (b : *) . `
-- - Lambdas: `\ (x : Maybe a) (y : a) . `
-- - If/then/else: `if @resultType (x == y) then expr1 else expr2`
-- - Case statements:
--   `case @type @resultType x of {pattern1 -> expr1 ; pattern2 -> expr2}`
-- - Bottom: `bottom @resultType`
-- - Type and term application: `f @a @b x @c y z`
parseTerm :: forall lang. (LanguageParser lang) => Parser (Expr lang)
parseTerm = P.label "Term" $ makeExprParser pAtom ops
  where
    ops =
      [InfixL (return ExprApp)] :
      operators @lang

    pAbs :: Parser (Expr lang)
    pAbs = do
      P.try (symbol "/\\")
      parseBinder
        ExprAbs
        (parseBinderNames (ident @lang) (parseTyOf >> parseKind))
        (symbol "." >> parseTerm)

    pLam :: Parser (Expr lang)
    pLam = do
      P.try (symbol "\\")
      parseBinder
        ExprLam
        (parseBinderNames (ident @lang) (parseTyOf >> parseType))
        (symbol "." >> parseTerm)

    parseIf :: Parser (Expr lang)
    parseIf = do
      P.try (symbol "if")
      ty <- symbol "@" >> parseTypeAtom
      c <- parseTerm
      symbol "then"
      t <- parseTerm
      symbol "else"
      ExprIf ty c t <$> parseTerm

    parseBottom :: Parser (Expr lang)
    parseBottom = do
      P.try (symbol "bottom")
      ty <- symbol "@" >> parseTypeAtom
      return (ExprBottom ty)

    parseCase :: Parser (Expr lang)
    parseCase = do
      P.try (symbol "case")
      ty <- symbol "@" >> parseTypeAtom
      tyRes <- symbol "@" >> parseTypeAtom
      term <- parseTerm
      symbol "of"
      cases <-
        curlyBrackets $
          P.sepBy1
            ((,) <$> parsePattern <*> (symbol "->" >> parseTerm))
            (symbol ";")
      return (ExprCase ty tyRes term cases)

    pAtom :: Parser (Expr lang)
    pAtom =
      asum
        [ pAbs,
          pLam,
          parens parseTerm,
          parseIf,
          parseCase,
          parseBottom,
          ExprBase <$> P.try (parseBuiltinTerm @lang),
          ExprTy <$> (P.try (symbol "@") >> parseTypeAtom),
          ExprLit <$> P.try (parseConstant @lang),
          ExprVar <$> P.try (ident @lang <|> typeName @lang)
        ]

-- | Parse a pattern for use in case statements or function declarations.
-- The catch-all pattern is `_`.
parsePattern :: forall lang. LanguageParser lang => Parser (Pattern lang)
parsePattern =
  P.label "pattern" $
    asum
      [ parens parsePattern,
        PatternAll <$ symbol "_",
        PatternConstr <$> constructorName @lang <*> many parsePattern,
        PatternVar <$> ident @lang
      ]

-- | "type of" and "kind of" symbol
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

-- | Parse a declaration of a type variable and its kind. The kind is `*` by
-- default if omitted.
-- E.g. `(a : * -> * -> *)`
-- E.g. `(a : *)` and `a` are equivalent
parseTypeVarKind :: forall lang. LanguageParser lang => Parser (String, SystF.Kind)
parseTypeVarKind = parens p <|> p
  where
    p =
      (,)
        <$> ident @lang
        <*> (P.try (parseTyOf *> parseKind) <|> return SystF.KStar)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

skipEmptyLine :: Parser ()
skipEmptyLine = P.try (hspaceComment <* P.newline)

hspaceComment :: Parser ()
hspaceComment = do
  P.hspace
  P.try (L.skipLineComment "--") <|> return ()

-- | Parse content in a line-folded fashion. The initial column number serves
-- as a reference. Every line that begins after that indentation level is
-- considered to be part of the line-folded section. The first line that goes
-- back to a lower indentation level marks the end of the line-folded section.
--
-- "lineFold" is expected to be applied to parsers that use "spaceConsumer"
-- exclusively.
--
-- For now, only basic top-level line folding is supported. A runtime error is
-- raised if line-folded sections are nested.
--
-- Note that, as long as lines begin after the reference column, they are
-- considered part of the section. This means that a three line block whose
-- lines start at columns 1, 4, then 2, is valid. Using the first indented line
-- as a reference (4 in this example) would require "State" instead of
-- "Reader" or cumbersome and ineffient look aheads.
lineFold :: Parser a -> Parser a
lineFold p = do
  P.SourcePos _ _ currentCol <- P.getSourcePos
  ask >>= \case
    Nothing -> local (const (Just currentCol)) p <* spaceConsumer
    Just _ -> error "nested line fold is unsupported"

-- | Space consumer compatible with "lineFold"
spaceConsumer :: Parser ()
spaceConsumer =
  ask >>= \case
    Nothing -> spaceConsumerOld
    Just startCol -> do
      hspaceComment
      asum
        [ P.try $ do
            _ <- P.newline
            _ <- many skipEmptyLine
            _ <- P.hspace
            P.SourcePos _ _ currentCol <- P.getSourcePos
            if P.unPos currentCol > P.unPos startCol
              then return ()
              else fail "not indented enough to line fold",
          return ()
        ]

-- | Default megaparsec space consumer (incompatible with "lineFold")
spaceConsumerOld :: Parser ()
spaceConsumerOld = L.space P.space1 (L.skipLineComment "--") empty

symbol :: String -> Parser ()
symbol = void . L.symbol spaceConsumer

keywords :: Set String
keywords =
  Set.fromList
    [ "case",
      "data",
      "forall",
      "destructor",
      "nonrec",
      "of",
      "if",
      "then",
      "else",
      "bottom"
    ]

-- | Parse an expression in parenthesis
parens :: Parser a -> Parser a
parens a = P.try (symbol "(") *> a <* symbol ")"

-- | Parse an expression in curly brackets
curlyBrackets :: Parser a -> Parser a
curlyBrackets a = P.try (symbol "{") *> a <* symbol "}"

-- | Parse identifiers starting with a lowercase letter or "_"
lowercaseIdent :: forall lang. (LanguageParser lang) => Set String -> Parser String
lowercaseIdent reserved = do
  i <- lexeme ((:) <$> (P.lowerChar <|> P.char '_') <*> restOfName)
  guard (i `Set.notMember` Set.union keywords reserved)
  return i

-- | Parse identifiers starting with a capitalized letter
uppercaseIdent :: forall lang. (LanguageParser lang) => Set String -> Parser String
uppercaseIdent reserved = do
  i <- lexeme ((:) <$> P.upperChar <*> restOfName)
  guard (i `Set.notMember` Set.union keywords reserved)
  return i

-- | Parse remaining allowed characters in identifiers (alphanumeric and "_")
restOfName :: Parser String
restOfName = many (P.alphaNumChar <|> P.oneOf ('_' : monoNameSep))

-- | Parse a declared or builtin type name (no type variable)
typeName :: forall lang. (LanguageParser lang) => Parser String
typeName =
  P.label "type-identifier" $
    uppercaseIdent @lang (reservedTypeNames @lang)

-- | Parse the name of a data constructor
constructorName :: forall lang. (LanguageParser lang) => Parser String
constructorName =
  P.label "constructor identifier" $
    uppercaseIdent @lang (reservedTermNames @lang)

-- | Parse the name of a function or variable identifier
ident :: forall lang. (LanguageParser lang) => Parser String
ident =
  P.label "identifier" $
    lowercaseIdent @lang (reservedTermNames @lang)
