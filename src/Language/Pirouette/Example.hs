{-# LANGUAGE TypeApplications #-}
-- | Exports the builtin types and quasiquoters for easily writing pirouette terms
--  Check the @tests/unit/Language/Pirouette/ExampleSpec.hs@ tests to see these
--  quasiquoters in action.
module Language.Pirouette.Example (module X, prog, progNoTC, term, ty) where

import qualified Language.Pirouette.QuasiQuoter as QQ
import Language.Pirouette.Example.Syntax as X (Ex, ExConstant, ExTerm, ExType)

prog :: QQ.QuasiQuoter
prog = QQ.prog @Ex

progNoTC :: QQ.QuasiQuoter
progNoTC = QQ.progNoTC @Ex

term :: QQ.QuasiQuoter
term = QQ.term @Ex

ty :: QQ.QuasiQuoter
ty = QQ.ty @Ex
