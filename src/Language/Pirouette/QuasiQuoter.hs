{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Provides the quasiquoters to be able to write @lang@ programs
--  directly into Haskell source files. Using the functions
--  exported by this module requires the @-XQuasiQuotes@ extension.
--  Check "Language.Pirouette.Example.QuasiQuoter" for an example instantiation.
module Language.Pirouette.QuasiQuoter (QuasiQuoter, prog, progNoTC, term, ty) where

import Control.Monad.Except (runExcept)
import qualified Data.Map as M
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax hiding (Name, Type)
import Language.Pirouette.QuasiQuoter.Syntax
import Language.Pirouette.QuasiQuoter.ToTerm
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.Pretty.Class (Pretty (..))
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Term.TypeChecker (typeCheckDecls, typeCheckFunDef)
import Text.Megaparsec

prog :: forall lang . (LanguageParser lang, LanguageBuiltinTypes lang, Language lang) => QuasiQuoter
prog = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseProgram @lang) <* eof) str
  (decls, DFunDef main@(FunDef _ mainTm _)) <- trQ (uncurry trProgram p0)
  _ <- maybeQ (typeCheckDecls decls)
  _ <- maybeQ (typeCheckFunDef decls "main" main)
  [e|(decls, mainTm)|]

progNoTC :: forall lang . (LanguageParser lang, Language lang) => QuasiQuoter
progNoTC = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseProgram @lang) <* eof) str
  (decls, DFunDef (FunDef _ mainTm _)) <- trQ (uncurry trProgram p0)
  [e|(decls, mainTm)|]

term :: forall lang . (LanguageParser lang, Language lang) => QuasiQuoter
term = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseTerm @lang) <* eof) str
  p1 <- trQ (trTerm [] [] p0)
  [e|p1|]

ty :: forall lang . (LanguageParser lang, Language lang) => QuasiQuoter
ty = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseType @lang) <* eof) str
  p1 <- trQ (trType [] p0)
  [e|p1|]

-- * Internals

parseQ :: Parser a -> String -> Q a
parseQ p str = case parse p "<template-haskell>" str of
  Left err -> fail (errorBundlePretty err)
  Right r -> return r

trQ :: TrM a -> Q a
trQ f = case runExcept f of
  Left err -> fail err
  Right r -> return r

maybeQ :: (Pretty e) => Either e a -> Q a
maybeQ (Left e) = fail $ show $ pretty e
maybeQ (Right x) = return x

instance (Lift k, Lift v) => Lift (M.Map k v) where
  liftTyped m = unsafeTExpCoerce [e|M.fromList $(lift (M.toList m))|]

quoter :: (String -> Q Exp) -> QuasiQuoter
quoter quote =
  QuasiQuoter
    { quoteExp = quote,
      quotePat = \_ -> failure0 "patterns",
      quoteType = \_ -> failure0 "types",
      quoteDec = \_ -> failure0 "declarations"
    }
  where
    failure0 k =
      fail ("this quasiquoter does not support splicing " ++ k)

-- Orphan instances to 'Lift' the necessary types

deriving instance Lift ann => Lift (SystF.Ann ann)

deriving instance Lift Namespace

deriving instance Lift Name

deriving instance Lift SystF.Kind

deriving instance (Lift (Constants lang), Lift (BuiltinTypes lang), Lift (BuiltinTerms lang)) => Lift (TermBase lang)

deriving instance (Lift (Constants lang), Lift (BuiltinTypes lang), Lift (BuiltinTerms lang)) => Lift (Var lang)

deriving instance Lift (BuiltinTypes lang) => Lift (TypeBase lang)

deriving instance Lift (BuiltinTypes lang) => Lift (TyVar lang)

deriving instance Lift (BuiltinTypes lang) => Lift (Type lang)

deriving instance (Lift (Constants lang), Lift (BuiltinTypes lang), Lift (BuiltinTerms lang)) => Lift (Arg lang)

deriving instance (Lift (Constants lang), Lift (BuiltinTypes lang), Lift (BuiltinTerms lang)) => Lift (Term lang)

deriving instance Lift Rec

deriving instance (Lift (Constants lang), Lift (BuiltinTypes lang), Lift (BuiltinTerms lang)) => Lift (FunDef lang)

deriving instance Lift (BuiltinTypes lang) => Lift (TypeDef lang)

deriving instance (Lift (Constants lang), Lift (BuiltinTypes lang), Lift (BuiltinTerms lang)) => Lift (Definition lang)
