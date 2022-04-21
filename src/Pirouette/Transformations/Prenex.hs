{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Pirouette.Transformations.Prenex (prenex) where

import qualified Data.Map as Map
import Optics.Core (over)
import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Subst (shift)
import qualified Pirouette.Term.Syntax.SystemF as SystemF

-- | * Prenex form of types
--
-- This transformation tries to push the type abstractions
-- (big lambdas @/\ x : Type .@ ) to the front of terms,
-- before any term abstractions (small lambdas @\ x : Int .@ )
--
-- For example,
-- >  /\ a : Type . \ x : a . /\ b : Type . \ y : b . ...
-- is transformed to
-- >  /\ a : Type . /\ b : Type . \ x : a . \ y : b . ...
--
-- This makes it easier for later transformations to apply
-- on type abstractions. In fact, it's common to just bail
-- out on non-prenex types in other transformations, because
-- those cases are quite rare and difficult to handle
-- (usually involving some impredicative types.)
prenex ::
  PrtUnorderedDefs lang ->
  PrtUnorderedDefs lang
prenex PrtUnorderedDefs {prtUODecls, prtUOMainTerm} = do
  -- this is done in two steps
  -- step 1. prenexify the types and lambdas
  let prenexDecls = Map.map prenexDefinitionLambdas prtUODecls
  -- step 2. prenixify the bodies
  PrtUnorderedDefs
    { prtUODecls = Map.map (prenexDefinitionBody prenexDecls) prenexDecls,
      prtUOMainTerm = prenexExpr prenexDecls prtUOMainTerm
    }

-- | Update the type and initial lambdas
-- from a definition. This *must* be followed
-- by 'prenexDefinitionBody' at a later point
-- to make everything correct.
prenexDefinitionLambdas ::
  Definition lang ->
  Definition lang
prenexDefinitionLambdas = over _DFunDef $ \FunDef {..} ->
  let (newTy, newBody) = switchLambdas funTy funBody
   in FunDef {funIsRec, funTy = newTy, funBody = newBody}

-- invariant: in the result type all /\ appear before all \
switchLambdas :: Type lang -> Term lang -> (Type lang, Term lang)
-- this case pushes lambdas inwards
-- \ x . /\ a . ty --> /\ a . \x . ty
switchLambdas
  (SystemF.TyFun ty1 (SystemF.TyAll annTy kindTy restOfType))
  (SystemF.Lam arg1 tyTm1 (SystemF.Abs annTm kindTm body)) =
    let -- since we are going to have an additional /\ on front,
        -- we need to shift the bound variables by 1
        shiftedTy1 = shift 1 ty1
        shiftedTyTm1 = shift 1 tyTm1
        (newTy, newBody) =
          switchLambdas
            (SystemF.TyFun shiftedTy1 restOfType)
            (SystemF.Lam arg1 shiftedTyTm1 body)
     in (SystemF.TyAll annTy kindTy newTy, SystemF.Abs annTm kindTm newBody)
-- case of small lambda, we just need to keep the invariant (see *)
switchLambdas (SystemF.TyFun ty1 ty2) (SystemF.Lam arg1 tyTm1 body) =
  let (newTy, newBody) = switchLambdas ty2 body
      newTy' = SystemF.TyFun ty1 newTy
      newBody' = SystemF.Lam arg1 tyTm1 newBody
   in case newTy of
        -- (*) when we have a /\ on the top we are breaking the invariant
        -- so run this again until everything is fine
        SystemF.TyAll {} -> switchLambdas newTy' newBody'
        _ -> (newTy', newBody')
-- if we have a big lambda, just leave it
switchLambdas
  (SystemF.TyAll annTy kindTy restOfType)
  (SystemF.Abs annTm kindTm body) =
    let (newTy, newBody) = switchLambdas restOfType body
     in (SystemF.TyAll annTy kindTy newTy, SystemF.Abs annTm kindTm newBody)
switchLambdas otherTy otherTm = (otherTy, otherTm)

-- | Update the body of a definition
-- with the prenex-ed types from 'newDecls'.
prenexDefinitionBody ::
  Decls lang ->
  Definition lang ->
  Definition lang
prenexDefinitionBody newDecls = over _DFunDef $ \funDef ->
  funDef {funBody = prenexExpr newDecls (funBody funDef)}

prenexExpr ::
  forall lang.
  Decls lang ->
  Term lang ->
  Term lang
prenexExpr newDecls = goTerm
  where
    goTerm :: Term lang -> Term lang
    goTerm (SystemF.Lam ann ty body) = SystemF.Lam ann ty (goTerm body)
    goTerm (SystemF.Abs ann ki body) = SystemF.Abs ann ki (goTerm body)
    goTerm (SystemF.App hd args) =
      let prenexArgs = map goArg args
       in case hd of
            -- we only change the applications of known names
            SystemF.Free (TermSig name)
              | Just (DFunDef FunDef {funTy}) <- Map.lookup name newDecls ->
                SystemF.App hd (zipArgs prenexArgs funTy)
            _other -> SystemF.App hd prenexArgs

    goArg (SystemF.TermArg e) = SystemF.TermArg (goTerm e)
    goArg (SystemF.TyArg ty) = SystemF.TyArg ty -- type arguments don't change

    -- no more arguments
    zipArgs [] _ = []
    zipArgs args (SystemF.TyAll _ _ restOfTy) = case SystemF.firstTyArg args of
      Nothing -> args -- none was found, just use arg as is
      Just (ty, moreArgs) -> ty : zipArgs moreArgs restOfTy
    zipArgs args (SystemF.TyFun _ restOfTy) = case SystemF.firstTermArg args of
      Nothing -> args -- none was found, just use arg as is
      Just (ty, moreArgs) -> ty : zipArgs moreArgs restOfTy
    zipArgs args _ = args
