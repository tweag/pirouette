{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Pirouette.Symbolic.Eval.Types where

import Data.Data hiding (eqT)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.String (IsString)
import Pirouette.Monad
import qualified Pirouette.SMT.Base as SMT
import qualified Pirouette.SMT.Constraints as SMT
import Pirouette.Term.Syntax
import Prettyprinter hiding (Pretty (..))
import qualified PureSMT

-- | The 'LanguageSymEval' class is used to instruct the symbolic evaluator on how to branch on certain builtins.
-- It is inherently different from 'SMT.LanguageSMT' in the sense that, for instance, the 'SMT.LanguageSMT'
-- translation of a primitive @if@ statement might use the @ifthenelse@ SMT primitive. However, the
-- 'LanguageSymEval' should instruct the symbolic evaluation engine on how to branch when that primitive is found.
-- In particular, two branches should be created:
--
--   1. Add @condition = True@ to the list of known things, continue with the then term,
--   2. Add @condition = False@ to the list of known things, continue with the else term.
--
-- This is the topmost class in the Pirouette universe, the relation between all the classes is:
--
-- > LanguageBuiltins --> defines the built-ins (both terms and types)
-- >   |     \
-- >   |      LanguageBuiltinTypes --> defines the typing rules of each built-in term
-- >   |
-- > LanguageSMT --> defines translation of built-ins into SMT
-- >   |             (not every term can be translated)
-- >   |
-- > LanguageSymEval --> defines at which points the symbolic evaluator has to do sth. special
class (SMT.LanguageSMT lang) => LanguageSymEval lang where
  -- | Injection of different cases in the symbolic evaluator.
  -- For example, one can introduce a 'if_then_else' built-in
  -- and implement this method to look at both possibilities.
  branchesBuiltinTerm ::
    (SMT.ToSMT meta, PirouetteReadDefs lang m) =>
    BuiltinTerms lang ->
    (TermMeta lang meta -> m (Maybe PureSMT.SExpr)) ->
    [ArgMeta lang meta] ->
    m (Maybe [SMT.Branch lang meta])
  branchesBuiltinTerm _ _ _ = pure Nothing

newtype SymVar = SymVar {symVar :: Name}
  deriving (Eq, Show, Data, Typeable, IsString)

instance Pretty SymVar where
  pretty (SymVar n) = pretty n

instance SMT.ToSMT SymVar where
  translate = SMT.translate . symVar

type Constraint lang = SMT.Constraint lang SymVar

symVarEq :: SymVar -> SymVar -> Constraint lang
symVarEq a b = SMT.And [SMT.VarEq a b]

(=:=) :: SymVar -> TermMeta lang SymVar -> Constraint lang
a =:= t = SMT.And [SMT.Assign a t]

data PathStatus = Completed | OutOfFuel deriving (Eq, Show)

instance Pretty PathStatus where
  pretty Completed = "Completed"
  pretty OutOfFuel = "OutOfFuel"

data Path lang res = Path
  { pathConstraint :: Constraint lang,
    pathGamma :: M.Map Name (Type lang),
    pathStatus :: PathStatus,
    pathResult :: res
  }
  deriving (Functor, Traversable, Foldable)

deriving instance (Eq (Constraint lang), Eq (Type lang), Eq res) => Eq (Path lang res)

deriving instance (Show (Constraint lang), Show (Type lang), Show res) => Show (Path lang res)

instance (LanguagePretty lang, Pretty a) => Pretty (Path lang a) where
  pretty (Path conds _gamma ps res) =
    vsep
      [ "", -- "Env:" <+> hsep (map pretty (M.toList gamma)),
        "Path:" <+> indent 2 (pretty conds),
        "Status:" <+> pretty ps,
        "Tip:" <+> indent 2 (pretty res)
      ]

data AvailableFuel = Fuel Int | InfiniteFuel
  deriving (Eq, Show)

data SymEvalSt lang = SymEvalSt
  { sestConstraint :: Constraint lang,
    sestGamma :: M.Map Name (Type lang),
    sestFreshCounter :: Int,
    sestStatistics :: SymEvalStatistics,
    -- | A branch that has been validated before is never validated again /unless/ we 'learn' something new.
    sestValidated :: Bool,
    sestKnownNames :: S.Set Name, -- The set of names the SMT solver is aware of
    sestStoppingCondition :: StoppingCondition
  }

instance (LanguagePretty lang) => Pretty (SymEvalSt lang) where
  pretty SymEvalSt {..} =
    "Constraints are" <+> pretty sestConstraint <> "\n"
      <> "in environnement"
      <+> pretty (M.toList sestGamma)
      <> "\n"
      <> "with a counter at"
      <+> pretty sestFreshCounter
      <+> "and"
      <+> pretty (sestConsumedFuel sestStatistics)
      <+> "fuel consumed"

data SymEvalStatistics = SymEvalStatistics
  { sestConsumedFuel :: Int,
    sestConstructors :: Int
  }
  deriving (Eq, Show)

type StoppingCondition = SymEvalStatistics -> Bool

instance Semigroup SymEvalStatistics where
  SymEvalStatistics f1 c1 <> SymEvalStatistics f2 c2 =
    SymEvalStatistics (f1 + f2) (c1 + c2)

instance Monoid SymEvalStatistics where
  mempty = SymEvalStatistics 0 0

-- | Given a result and a resulting state, returns a 'Path' representing it.
path :: a -> SymEvalSt lang -> Path lang a
path x st =
  Path
    { pathConstraint = sestConstraint st,
      pathGamma = sestGamma st,
      pathStatus = if sestStoppingCondition st (sestStatistics st) then OutOfFuel else Completed,
      pathResult = x
    }
