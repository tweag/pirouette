{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}

module Pirouette.Symbolic.ProveSpec.Internal where

import Control.Monad.Reader
import Data.Default
import Data.Maybe (isJust)
import Language.Pirouette.Example
import qualified Language.Pirouette.Example.IsUnity as IsUnity
import Language.Pirouette.Example.StdLib (stdLib)
import Pirouette.Monad
import Pirouette.Symbolic.Eval
import Pirouette.Symbolic.EvalUtils
import Pirouette.Symbolic.Prover
import Pirouette.Term.Syntax
import Pirouette.Transformations (elimEvenOddMutRec)
import Pirouette.Transformations.Defunctionalization
import Pirouette.Transformations.EtaExpand
import Pirouette.Transformations.Monomorphization
import qualified PureSMT
import Test.Tasty
import Test.Tasty.HUnit

exec ::
  (Problem Ex -> ReaderT (PrtOrderedDefs Ex) IO a) ->
  (PrtUnorderedDefs Ex, Type Ex, Term Ex) ->
  (Term Ex, Term Ex) ->
  IO a
exec toDo (decls, tyRes, fn) (assume, toProve) = do
  let orderedDecls = elimEvenOddMutRec decls
  flip runReaderT orderedDecls $
    toDo (Problem tyRes fn assume toProve)
