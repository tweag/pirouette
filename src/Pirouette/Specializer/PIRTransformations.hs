{-# LANGUAGE OverloadedStrings #-}

module Pirouette.Specializer.PIRTransformations where

import Data.Text as T
import Pirouette.Specializer.Rewriting

allRewRules :: [RewritingRule T.Text T.Text]
allRewRules =
  [ -- Removes superfluous Bool-match. For example,
    -- > [b/ifThenElse [b/greaterThanEqualsInteger m n] c/True/Bool c/False/Bool]
    -- Could be simply:
    -- > [b/greaterThanEqualsInteger m n]

    -- WARNING: Before specializing plutus booleans to TLA booleans, this transformation broke things.
    -- In the example above, @b/greaterThanEqualsInteger@ was a plutus builtin boolean,
    -- whereas the @ifThenElse@ returned an element of a @(datatypedecl ... Bool)@.

    RewritingRule
      { name = "etaIfThenElse",
        lhs = "[[[{(builtin ifThenElse) A1_} x2_ ] True] False]",
        rhs = "x2_"
      },
    -- Even if TLA+ is untyped, there are strong constraints regarding arity of operators.
    -- The two foldableNil transformations aims at getting rid of the functions passed to a type constructor, here CConsMonoid.
    -- Since passing function to a polymorphic operator should be avoided too, we make a special case of this apecilization for endofunctors.

    -- This transformation assumes that the only monoid with a functional type
    -- and which has the identity as a neutral element is the endofunctor monoid, with composition.

    RewritingRule
      { name = "foldableNilEndo",
        lhs = "[[[[{{fFoldableNil_cfoldMap m0_} a1_} [[{CConsMonoid (fun t21_ t22_)} o3_] (lam x T4_ x)]] f5_] l6_] x7_]",
        rhs = "[[[{{foldr a1_} t22_} (lam aSpz a1_ (lam bSpz t22_ [[f5_ aSpz] bSpz]))] x7_] l6_]"
      },
    RewritingRule
      { name = "foldableNilOther",
        lhs = "[[[{{fFoldableNil_cfoldMap m0_} a1_} [[{CConsMonoid t2_} o3_] n4_]] f5_] l6_]",
        rhs = "[[[{{foldr a1_} t2_} (lam aSpz a1_ (lam bSpz t2_ [[o3_ [f5_ aSpz]] bSpz]))] n4_] l6_]"
      }
  ]
