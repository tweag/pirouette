{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MonoLocalBinds #-}
module Pirouette.Symbolic.Eval.Types where

import Data.Data hiding (eqT)
import qualified Data.Map.Strict as M
import Data.String (IsString)
import qualified Pirouette.SMT.Base as SMT
import qualified Pirouette.SMT.Constraints as SMT
import Pirouette.Term.Syntax
import Prettyprinter hiding (Pretty (..))
import qualified Data.Set as S

-- import Debug.Trace (trace)

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
