{-# LANGUAGE TypeApplications #-}
module Language.Pirouette.PlutusIR (module X, pir) where

import Language.Pirouette.PlutusIR.Typing as X ()
import Language.Pirouette.PlutusIR.Syntax as X
import Language.Pirouette.PlutusIR.SMT as X
import Language.Pirouette.PlutusIR.ToTerm as X (trProgram, trProgramDecls)

import qualified Language.Pirouette.QuasiQuoter as QQ

pir :: QQ.QuasiQuoter
pir = QQ.term @PlutusIR
