-- | Whenever you are defining a language @L@ and you want to symbolically
--  evaluate it, you will need to define an instance for
--  'Pirouette.Symbolic.Eval.Types.LanguageSymEval'. This module contains
--  definitions to help defining branching for different possible builtins
module Pirouette.Symbolic.Eval.BranchingHelpers where

import Pirouette.Monad
import Pirouette.SMT
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF

-- | A standard way of instruction the symbolic engine how to branch on if-statements
ifThenElseBranching ::
  (Applicative f, LanguageSMT lang, Show meta) =>
  (TermMeta lang meta -> Bool) ->
  TermMeta lang meta ->
  (TermMeta lang meta -> Bool) ->
  TermMeta lang meta ->
  (BuiltinTerms lang -> Bool) ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  TermMeta lang meta ->
  [ArgMeta lang meta] ->
  f (Maybe [Branch lang meta])
ifThenElseBranching isTrue trueTm isFalse falseTm isEq c t e excess =
  let t' = t `SystF.appN` excess
      e' = e `SystF.appN` excess
   in case c of
        _ | isTrue c -> pure $ Just [Branch mempty t]
        _ | isFalse c -> pure $ Just [Branch mempty e]
        SystF.App (SystF.Free (Builtin eq)) [SystF.TermArg x, SystF.TermArg y]
          -- try to generate the best type of constraint
          -- from the available equality ones
          | isEq eq,
            Just x1 <- termIsMeta x,
            Just y1 <- termIsMeta y ->
            pure $
              Just
                [ -- either they are equal
                  Branch [symVarEq x1 y1] t',
                  -- or they are not
                  Branch [termEq x y] e'
                ]
          | isEq eq,
            Just x1 <- termIsMeta x,
            isStuckBuiltin y ->
            pure $
              Just
                [ -- either they are equal
                  Branch [x1 =:= y] t',
                  -- or they are not
                  Branch [termNotEq x y] e'
                ]
          | isEq eq,
            isStuckBuiltin x,
            Just y1 <- termIsMeta y ->
            pure $
              Just
                [ -- either they are equal
                  Branch [y1 =:= x] t',
                  -- or they are not
                  Branch [termNotEq y x] e'
                ]
          | isEq eq,
            isStuckBuiltin x,
            isStuckBuiltin y ->
            pure $
              Just
                [ -- either they are equal
                  Branch [termEq x y] t',
                  -- or they are not
                  Branch [termNotEq x y] e'
                ]
        _
          | Just v <- termIsMeta c ->
            pure $
              Just
                [ -- c is True => t is executed
                  Branch [v =:= trueTm] t',
                  -- c is False => e is executed
                  Branch [v =:= falseTm] e'
                ]
        _ -> pure Nothing
