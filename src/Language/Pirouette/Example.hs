{-# LANGUAGE QuasiQuotes #-}
module Language.Pirouette.Example ( module X ) where

import Language.Pirouette.Example.Syntax as X
import Language.Pirouette.Example.ToTerm as X
import Language.Pirouette.Example.QuasiQuoter as X
import Pirouette.Term.Syntax.Base

xxx :: Term Ex
xxx = [term| \a :: Integer . a + a |]
