{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Pirouette.SMT.Constraints where

import Control.Monad.IO.Class
import Data.Bifunctor (bimap)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Void
import Pirouette.SMT.Common
import Pirouette.SMT.Datatypes
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.SystemF
import qualified PlutusCore as P
import Data.Maybe (mapMaybe)
import Data.Text.Prettyprint.Doc hiding (Pretty (..))
import Data.List (intersperse)

-- | Bindings from names to types (for the assign constraints)
type Env = Map Name PrtType

-- | Constraints of a path during symbolic execution
-- We would like to have
-- type Constraint = Bot | And (Map Name [PrtTerm]) [(Fuel, PrtTerm, PrtTerm))]
-- It is isomorphic to our current type, but with better access time to the variable assignements.
-- The 2 kinds of equalities are quite different,
-- one represents the complete execution of a branch, which leads to an application which cannot be further inlined
-- (Because it is a builtin or a constant),
-- whereas the other one represents an ongoing computation killed by lack of fuel.
data Constraint
  = Assign Name PrtTerm
  | NonInlinableSymbolEq PrtTerm PrtTerm
  | OutOfFuelEq PrtTerm PrtTerm
  | And [Constraint]
  | Bot

instance Pretty Constraint where
  pretty (Assign n term) =
    pretty n <+> "↦" <+> pretty term
  pretty (NonInlinableSymbolEq t u) =
    pretty t <+> "==" <+> pretty u
  pretty (OutOfFuelEq t u) =
    pretty t <+> "~~" <+> pretty u
  pretty Bot =
    "⊥"
  pretty (And []) =
    "⊤"
  pretty (And l) =
    mconcat $ intersperse "\n∧ " (map pretty l)

-- | Declare constants and assertions in an SMT solver based on a constraint
-- that characterizes a path in the symbolic execution of a Plutus IR term.
--
-- We cannot just generate SExpr for smtlib (instantiating the Translatable
-- class) because of Assign constraints which need to declare names as a side
-- effect and And constraints which need to run these declarations in the right
-- order.
--
-- There is an issue for now when generating assertions such as:
-- x : Bool
-- x = Nil
-- because Nil has type List a. Nil must be applied to Bool.
--
-- There are three ways to sort things out:
--
-- 1. Use SMTlib's "match" term
-- e.g. assert ((match x ((Nil true) ((Cons y ys) false))))
--
-- 2. Use the weird "as" SMTLib term
-- assert (= x (as Nil (List Bool)))
-- The weird thing is that Cons should be "cast"/"applied"/"coerced" (which is
-- right?) to List Bool as well although it is a constructor of arity > 0
-- The "as" term seems to mean "here *** is a constructor of that concrete
-- type", but it is not type application
--
-- 3. Use the, weird as well, "_ is" template/function/whatever
-- (assert ((_ is Nil) x))
-- In our case, it seems to be a shortcut that is equivalent to #1
--
-- All these solutions could lead to the same sat result and examples.
-- However, solution #2 presents the advantage that it allows to give names to the argument of constructors,
-- which can then be used in further constraints.
--
-- Hence, we chose solution #2
assertConstraint :: MonadIO m => SmtLib.Solver -> Env -> Constraint -> m ()
assertConstraint s env (Assign name term) =
  do
    let smtName = toSmtName name
    let (Just ty) = Map.lookup name env
    liftIO $
      SmtLib.assert s (SmtLib.symbol smtName `SmtLib.eq` translateData ty term)
assertConstraint s _ (NonInlinableSymbolEq term1 term2) =
  liftIO $ SmtLib.assert s (translate term1 `SmtLib.eq` translate term2)
assertConstraint s _ (OutOfFuelEq term1 term2) =
  liftIO $ SmtLib.assert s (translate term1 `SmtLib.eq` translate term2)
assertConstraint s env (And constraints) =
  sequence_ (assertConstraint s env <$> constraints)
assertConstraint s _ Bot = liftIO $ SmtLib.assert s (SmtLib.bool False)

-- | Declare (name and type) all the variables of the environment in the SMT
-- solver. This step is required before asserting constraints on these
-- variables.
declareVariables :: MonadIO m => SmtLib.Solver -> Env -> m ()
declareVariables s env =
  liftIO $
    sequence_
      ( uncurry (SmtLib.declare s)
          . bimap toSmtName translate
          <$> Map.toList env
      )

-- | In `Assign` constraints, the assigned terms are always fully-applied
-- constructors. This dedicated translation function provides required type
-- annotation for the SMT. For example Nil may have a List Int annotation (the
-- `as` term in smtlib). Besides, this function removes applications of types
-- to terms ; they do not belong in the term world of the resulting smtlib
-- term.
translateData :: PrtType -> PrtTerm -> SmtLib.SExpr
translateData ty (App var@(B (Ann name) _) []) = translate var
translateData ty (App (F (FreeName name)) args) =
  SmtLib.app
    (SmtLib.as (SmtLib.symbol (toSmtName name)) (translate ty))
    (translateData ty <$> mapMaybe fromArg args)
translateData ty _ = error "Illegal term in translate data"

-- TODO: The translation of term is still to be worked on,
-- since it does not allow to use builtins or defined functions,
-- and it contains application of term to types,
-- A frequent situation in system F, but not allowed in the logic of SMT solvers.

instance Translatable (AnnTerm (AnnType Name (Var Name (TypeBase Name))) Name (Var Name (PIRBase P.DefaultFun Name))) where
  translate (App var args) = SmtLib.app (translate var) (translate <$> args)
  translate (Lam ann ty term) = error "Translate term to smtlib: Lambda abstraction in term"
  translate (Abs ann kind term) = error "Translate term to smtlib: Type abstraction in term"
  translate (Hole h) = error "Translate term to smtlib: Hole"

instance Translatable (Var Name (PIRBase P.DefaultFun Name)) where
  translate (B (Ann name) _) = SmtLib.symbol (toSmtName name)
  translate (F (FreeName name)) = SmtLib.symbol (toSmtName name)
  translate (F _) = error "Free variable translation not yet implemented."

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
  translate (Arg term) = translate term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
  translate (TyArg ty) = translate ty
