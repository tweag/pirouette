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

module Language.Pirouette.QuasiQuoter.Internal where

import Control.Monad.Except (runExcept)
import Control.Monad.Reader
import qualified Data.Map as M
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax hiding (Name, Type)
import Language.Pirouette.QuasiQuoter.Syntax
import Language.Pirouette.QuasiQuoter.ToTerm
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.Pretty.Class (Pretty (..))
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Text.Megaparsec

parseQ :: Parser a -> String -> Q a
parseQ p str =
  case runReader (runParserT p "<template-haskell>" str) Nothing of
    Left err -> fail (errorBundlePretty err)
    Right r -> return r

trQ :: TrM a -> Q a
trQ f = case runExcept f of
  Left err -> fail err
  Right r -> return r

maybeQ :: (Pretty e) => Either e a -> Q a
maybeQ (Left e) = fail $ show $ pretty e
maybeQ (Right x) = return x

instance (Ord k, Lift k, Lift v) => Lift (M.Map k v) where
  liftTyped m = [||M.fromList $$(liftTyped (M.toList m))||]

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
