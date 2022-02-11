{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

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
import Prettyprinter hiding (Pretty (..))
import Data.List (intersperse)

-- | Bindings from names to types (for the assign constraints)
type Env lang = Map Name (PrtType lang)

-- | Constraints of a path during symbolic execution
-- We would like to have
-- type Constraint = Bot | And (Map Name [PirTerm]) [(Fuel, PirTerm, PirTerm))]
-- It is isomorphic to our current type, but with better access time to the variable assignements.
-- The 2 kinds of equalities are quite different,
-- one represents the complete execution of a branch, which leads to an application which cannot be further inlined
-- (Because it is a builtin or a constant),
-- whereas the other one represents an ongoing computation killed by lack of fuel.
data Constraint lang meta
  = Assign Name (PrtTermMeta lang meta)
  | NonInlinableSymbolEq (PrtTermMeta lang meta) (PrtTermMeta lang meta)
  | OutOfFuelEq (PrtTermMeta lang meta) (PrtTermMeta lang meta)
  | And [Constraint lang meta]
  | Bot

instance Semigroup (Constraint lang meta) where
  (<>) = andConstr
instance Monoid (Constraint lang meta) where
  mempty = And []

-- Essentially list concatenation, with the specificity that `Bot` is absorbing.
andConstr :: Constraint lang meta -> Constraint lang meta -> Constraint lang meta
andConstr Bot _ = Bot
andConstr _ Bot = Bot
andConstr (And l) (And m) = And (l ++ m)
andConstr (And l) y = And (y : l)
andConstr x (And m) = And (x : m)
andConstr x y = And [x, y]

instance (PrettyLang lang, Pretty meta) => Pretty (Constraint lang meta) where
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
assertConstraint :: (LanguageSMT lang, ToSMT meta, MonadIO m)
  => SmtLib.Solver -> Env lang -> Constraint lang meta -> m ()
assertConstraint s env (Assign name term) =
  do
    let smtName = toSmtName name
    let (Just ty) = Map.lookup name env
    liftIO $
      SmtLib.assert s (SmtLib.symbol smtName `SmtLib.eq` translateData (prtTypeToMeta ty) term)
assertConstraint s _ (NonInlinableSymbolEq term1 term2) =
  liftIO $ SmtLib.assert s (translateTerm term1 `SmtLib.eq` translateTerm term2)
assertConstraint s _ (OutOfFuelEq term1 term2) =
  liftIO $ SmtLib.assert s (translateTerm term1 `SmtLib.eq` translateTerm term2)
assertConstraint s env (And constraints) =
  sequence_ (assertConstraint s env <$> constraints)
assertConstraint s _ Bot = liftIO $ SmtLib.assert s (SmtLib.bool False)

-- | Declare (name and type) all the variables of the environment in the SMT
-- solver. This step is required before asserting constraints on these
-- variables.
declareVariables :: (LanguageSMT lang, MonadIO m) => SmtLib.Solver -> Env lang -> m ()
declareVariables s env =
  liftIO $
    sequence_
      ( uncurry (SmtLib.declare s)
          . bimap toSmtName translateType
          <$> Map.toList env
      )

-- | In `Assign` constraints, the assigned terms are always fully-applied
-- constructors. This dedicated translation function provides required type
-- annotation for the SMT. For example Nil may have a List Int annotation (the
-- `as` term in smtlib). Besides, this function removes applications of types
-- to terms ; they do not belong in the term world of the resulting smtlib
-- term.
translateData :: (LanguageSMT lang, ToSMT meta)
  => PrtTypeMeta lang meta -> PrtTermMeta lang meta -> SmtLib.SExpr
translateData ty (App var@(B (Ann name) _) []) = translateVar var
translateData ty (App (F (FreeName name)) args) =
  SmtLib.app
    (SmtLib.as (SmtLib.symbol (toSmtName name)) (translateType ty))
    (translateData ty <$> mapMaybe fromArg args)
translateData ty _ = error "Illegal term in translate data"

-- TODO: The translation of term is still to be worked on,
-- since it does not allow to use builtins or defined functions,
-- and it contains application of term to types,
-- A frequent situation in system F, but not allowed in the logic of SMT solvers.
translateTerm :: (LanguageSMT lang, ToSMT meta) => PrtTermMeta lang meta -> SmtLib.SExpr
translateTerm (App var args) = SmtLib.app (translateVar var) (translateArg <$> args)
translateTerm (Lam ann ty term) = error "Translate term to smtlib: Lambda abstraction in term"
translateTerm (Abs ann kind term) = error "Translate term to smtlib: Type abstraction in term"

translateVar :: (LanguageSMT lang, ToSMT meta) => PrtVarMeta lang meta -> SmtLib.SExpr
translateVar (B (Ann name) _) = SmtLib.symbol (toSmtName name)
translateVar (F (FreeName name)) = SmtLib.symbol (toSmtName name)
translateVar (F _) = error "Free variable translation not yet implemented."
translateVar (M h) = translate h

translateArg :: (LanguageSMT lang, ToSMT meta) => PrtArgMeta lang meta -> SmtLib.SExpr
translateArg (Arg term) = translateTerm term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
translateArg (TyArg ty) = translateType ty

{-
instance Translatable (Var Name (TermBase PlutusIR Name)) where

instance Translatable (Arg PirTypeExpanded PirTermExpanded) where
  translate (Arg term) = translate term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
  translate (TyArg ty) = translate ty
-}
