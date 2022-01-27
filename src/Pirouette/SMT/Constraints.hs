{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Pirouette.SMT.Constraints where

import Data.Void
import Pirouette.SMT.Common
import Pirouette.SMT.Datatypes
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF
import qualified PlutusCore as P

-- | Constraints of a path during symbolic execution
data Constraint
  = Assign Name PrtType PrtTerm
  | OutOfFuelEq PrtTerm PrtTerm
  | And [Constraint]
  | Bot

-- | Declare constants and assertions in an SMT solver based on a constraint
-- that characterizes a path in the symbolic execution of a Plutus IR term.
--
-- We cannot just generate SExpr for smtlib (instantiating the Translatable
-- class) because of Assign constraints which need to declare names as a side
-- effect and And constraints which need to run these declarations in the right
-- order.
assertConstraint :: SmtLib.Solver -> Constraint -> IO ()
assertConstraint s (Assign name ty term) =
  do
    let smtName = toSmtName name
    SmtLib.declare s smtName (translate ty)
    SmtLib.assert s (SmtLib.symbol smtName `SmtLib.eq` translate term)
assertConstraint s (OutOfFuelEq term1 term2) =
  SmtLib.assert s (translate term1 `SmtLib.eq` translate term2)
assertConstraint s (And constraints) =
  sequence_ (assertConstraint s <$> constraints)
assertConstraint s Bot = SmtLib.assert s (SmtLib.bool False)

instance Translatable (AnnTerm (AnnType Name (Var Name (TypeBase Name))) Name (Var Name (PIRBase P.DefaultFun Name))) where
  translate (App var args) = SmtLib.app (translate var) (translate <$> args)
  translate (Lam ann ty term) = error "Translate term to smtlib: Lambda abstraction in term"
  translate (Abs ann kind term) = error "Translate term to smtlib: Type abstraction in term"
  translate (Hole h) = error "Translate term to smtlib: Hole"

instance Translatable (Var Name (PIRBase P.DefaultFun Name)) where
  translate (B (Ann name) _) = SmtLib.symbol (toSmtName name)
  translate (F _) = undefined

instance
  Translatable
    ( Arg
        (AnnType Name (Var Name (TypeBase Name)))
        ( AnnTermH
            Void
            (AnnType Name (Var Name (TypeBase Name)))
            Name
            (Var Name (PIRBase P.DefaultFun Name))
        )
    )
  where
  translate (TyArg ty) = translate ty
  translate (Arg term) = translate term
