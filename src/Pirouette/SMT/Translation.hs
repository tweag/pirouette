{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

-- | Translation of Pirouette syntactical categories into
-- smtlib through our copy of the SimpleSMT library.
module Pirouette.SMT.Translation where

import Control.Monad.Except
import Control.Monad.IO.Class
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Debug.Trace
import Pirouette.Monad
import Pirouette.SMT.Base
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF

-- * Translating Terms and Types to SMTLIB

-- |Checks whether we can translate the current datatype definitions and whether
-- the type of each term is amenable to translation. We won't try translating the terms
-- because these will contain bound variables that will need to be substituted by
-- the symbolic execution engine.
checkDefsToSMT :: (PirouetteReadDefs lang m, PrettyLang lang, LanguageSMT lang) => m ()
checkDefsToSMT = do
  allDefs <- prtAllDefs
  forM_ (M.toList allDefs) $ \(n, def) -> do
    case def of
      DFunction _red _term ty -> void $ translateType ty
      DTypeDef (Datatype _ _ _ constr) -> mapM_ constructorFromPIR constr
      _ -> return ()

translateTypeBase ::
  forall lang m.
  (LanguageSMT lang, MonadFail m) =>
  TypeBase lang Name ->
  m SmtLib.SExpr
translateTypeBase (TyBuiltin pirType) = return $ translateBuiltinType @lang pirType
translateTypeBase (TyFree name) = return $ SmtLib.symbol (toSmtName name)

translateType ::
  (LanguageSMT lang, ToSMT meta, MonadFail m) =>
  PrtTypeMeta lang meta ->
  m SmtLib.SExpr
translateType (TyApp (F ty) args) = SmtLib.app <$> translateTypeBase ty <*> mapM translateType args
translateType (TyApp (B (Ann ann) index) args) =
  SmtLib.app (SmtLib.symbol (toSmtName ann)) <$> mapM translateType args
translateType x = fail $ "Translate type to smtlib: cannot handle " <> show x

-- TODO: The translation of term is still to be worked on,
-- since it does not allow to use builtins or defined functions,
-- and it contains application of term to types,
-- A frequent situation in system F, but not allowed in the logic of SMT solvers.
translateTerm ::
  (LanguageSMT lang, ToSMT meta, MonadFail m) =>
  PrtTermMeta lang meta ->
  m SmtLib.SExpr
translateTerm (App var args) = SmtLib.app <$> translateVar var <*> mapM translateArg args
translateTerm (Lam ann ty term) = fail "Translate term to smtlib: Lambda abstraction in term"
translateTerm (Abs ann kind term) = fail "Translate term to smtlib: Type abstraction in term"

translateVar ::
  forall lang meta m.
  (LanguageSMT lang, ToSMT meta, MonadFail m) =>
  PrtVarMeta lang meta ->
  m SmtLib.SExpr
translateVar (M h) = return $ translate h
translateVar (F (FreeName name)) = return $ SmtLib.symbol (toSmtName name)
translateVar (F (Constant c)) = return $ translateConstant @lang c
translateVar (F (Builtin b)) = return $ translateBuiltinTerm @lang b
translateVar (B (Ann name) _) = fail "translateVar: Bound variable; did you forget to apply something?"
translateVar (F Bottom) = fail "translateVar: Bottom; unclear how to translate that. WIP"

translateArg ::
  (LanguageSMT lang, ToSMT meta, MonadFail m) =>
  PrtArgMeta lang meta ->
  m SmtLib.SExpr
translateArg (Arg term) = translateTerm term
-- TODO: This case is known to create invalid SMT terms,
-- since in SMT solver, application of a term to a type is not allowed.
translateArg (TyArg ty) = translateType ty

-- | The definition of constructors in SMTlib follows a fixed layout. This
-- function translates constructor types in PlutusIR to this layout and
-- provides required names for the fields of product types.
constructorFromPIR ::
  forall lang meta m.
  (LanguageSMT lang, ToSMT meta, MonadFail m) =>
  (Name, PrtTypeMeta lang meta) ->
  m (String, [(String, SmtLib.SExpr)])
constructorFromPIR (name, constructorType) =
  (toSmtName name,)
    .
    -- Fields of product types must be named: we append ids to the constructor name
    zip
      ((toSmtName name ++) . ("_" ++) . show <$> [1 ..])
    <$> aux constructorType
  where
    aux :: PrtTypeMeta lang meta -> m [SmtLib.SExpr]
    aux x = let (args, _) = tyFunArgs x in mapM translateType args
