{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Provides the quasiquoters to be able to write @lang@ programs
--  directly into Haskell source files. Using the functions
--  exported by this module requires the @-XQuasiQuotes@ extension.
--  Check "Language.Pirouette.Example.QuasiQuoter" for an example instantiation.
module Language.Pirouette.QuasiQuoter (QuasiQuoter, prog, progNoTC, term, ty, funDecl) where

import Language.Haskell.TH.Quote
import Language.Pirouette.QuasiQuoter.Internal
import Language.Pirouette.QuasiQuoter.Syntax
import Language.Pirouette.QuasiQuoter.ToTerm
import Pirouette.Term.Syntax.Base
import Pirouette.Term.TypeChecker (typeCheckDecls)
import Text.Megaparsec

prog :: forall lang. (LanguageParser lang, LanguageBuiltinTypes lang, LanguagePretty lang) => QuasiQuoter
prog = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseProgram @lang) <* eof) str
  decls <- trQ (trProgram p0)
  _ <- maybeQ (typeCheckDecls decls)
  [e|(PrtUnorderedDefs decls)|]

progNoTC :: forall lang. (LanguageParser lang, LanguagePretty lang) => QuasiQuoter
progNoTC = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseProgram @lang) <* eof) str
  decls <- trQ (trProgram p0)
  [e|(PrtUnorderedDefs decls)|]

term :: forall lang. (LanguageParser lang, LanguagePretty lang) => QuasiQuoter
term = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseTerm @lang) <* eof) str
  p1 <- trQ (trTerm [] [] p0)
  [e|p1|]

ty :: forall lang. (LanguageParser lang, LanguagePretty lang) => QuasiQuoter
ty = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme (parseType @lang) <* eof) str
  p1 <- trQ (trType [] p0)
  [e|p1|]

funDecl :: forall lang. (LanguageParser lang, Language lang) => QuasiQuoter
funDecl = quoter $ \str -> do
  (_, p0) <- parseQ (spaceConsumer *> lexeme (parseFunDecl @lang) <* eof) str
  p1 <- trQ (trFunDecl p0)
  [e|p1|]
