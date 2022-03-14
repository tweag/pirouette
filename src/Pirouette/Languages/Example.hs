{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
module Pirouette.Languages.Example ( module X ) where

import Pirouette.Term.Syntax.Base
import Pirouette.Term.Builtins
import Text.Megaparsec

import Pirouette.Languages.Example.Syntax as X
import Pirouette.Languages.Example.ToTerm as X
import Control.Monad.Except

test :: String -> IO (Either String (Type Ex))
test str = do
  case parseMaybe X.parseType str of
    Nothing -> error "No parse"
    Just ty -> return $ runExcept (trType [] ty)
