module Pirouette (module X) where

import Pirouette.Symbolic.Eval.Types as X
  ( StoppingCondition,
    SymEvalStatistics (..),
  )
import Pirouette.Symbolic.Prover.Runner as X
  ( AssumeProve (..),
    IncorrectnessParams (..),
    IncorrectnessResult,
    assertIncorrectnessLogic,
    replIncorrectnessLogic,
    replIncorrectnessLogicSingl,
  )

test :: Int
test =
  let x = 7 in
    case x of
      0 -> 2
      n -> n + 4
