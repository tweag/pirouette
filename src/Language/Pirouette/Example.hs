-- |Exports the builtin types and quasiquoters for easily writing pirouette terms
-- Check the @tests/unit/Language/Pirouette/ExampleSpec.hs@ tests to see these
-- quasiquoters in action.
module Language.Pirouette.Example ( module X ) where

import Language.Pirouette.Example.Syntax as X (Ex, ExType, ExTerm, ExConstant)
import Language.Pirouette.Example.QuasiQuoter as X (prog, term, ty)
