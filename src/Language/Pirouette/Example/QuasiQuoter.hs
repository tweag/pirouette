{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Pirouette.Example.QuasiQuoter (prog, term, ty) where

import Control.Monad.Except (runExcept)
import qualified Data.Map as M
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax hiding (Name, Type)
import Language.Pirouette.Example.Syntax
import Language.Pirouette.Example.ToTerm
import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Text.Megaparsec

prog :: QuasiQuoter
prog = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme parseProgram <* eof) str
  p1 <- trQ (uncurry trProgram p0)
  [e|p1|]

term :: QuasiQuoter
term = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme parseTerm <* eof) str
  p1 <- trQ (trTerm [] [] p0)
  [e|p1|]

ty :: QuasiQuoter
ty = quoter $ \str -> do
  p0 <- parseQ (spaceConsumer *> lexeme parseType <* eof) str
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

deriving instance Lift Name

deriving instance Lift SystF.Kind

deriving instance Lift (TermBase Ex)

deriving instance Lift (Var Ex)

deriving instance Lift (TypeBase Ex)

deriving instance Lift (TyVar Ex)

deriving instance Lift (Type Ex)

deriving instance Lift (Arg Ex)

deriving instance Lift (Term Ex)

deriving instance Lift Rec

deriving instance Lift (FunDef Ex)

deriving instance Lift (TypeDef Ex)

deriving instance Lift (Definition Ex)
