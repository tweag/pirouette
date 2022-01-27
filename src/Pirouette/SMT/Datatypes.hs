{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Translation of datatype declarations and type terms from
-- PlutusIR/Pirouette to smtlib through the SimpleSMT library.
module Pirouette.SMT.Datatypes where

import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Pirouette.Monad
import Pirouette.SMT.Common
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF

-- | Declare a datatype in the solver
declareDatatype :: Show name => SmtLib.Solver -> name -> TypeDef name -> IO ()
declareDatatype solver typeName typeDef@(Datatype _ typeVariabes _ constructors) =
  SmtLib.declareDatatype
    solver
    (toSmtName typeName)
    (map (toSmtName . fst) typeVariabes)
    (constructorFromPIR <$> constructors)

-- | The definition of constructors in SMTlib follows a fixed layout. This
-- function translates constructor types in PlutusIR to this layout and
-- provides required names for the fields of product types.
constructorFromPIR ::
  forall name builtins.
  TranslationConstraints name builtins =>
  (name, AnnType name (Var name builtins)) ->
  (String, [(String, SmtLib.SExpr)])
constructorFromPIR (name, constructorType) =
  ( toSmtName name,
    -- Fields of product types must be named:
    -- we append ids to the constructor name
    zip
      ((toSmtName name ++) . ("_" ++) . show <$> [1 ..])
      (aux constructorType)
  )
  where
    aux :: AnnType name (Var name builtins) -> [SmtLib.SExpr]
    aux x = let (args, _) = tyFunArgs x in map translate args

-- Declare all the datatypes in the solver from an ordered set of Pirouette
-- definitions
declareDatatypes :: SmtLib.Solver -> PrtOrderedDefs -> IO ()
declareDatatypes solver (PrtOrderedDefs decls orderedNames _) =
  let typeNames =
        mapMaybe
          (\case (TyArg name) -> Just name; _ -> Nothing)
          orderedNames
   in mapM_ aux typeNames
  where
    aux :: Name -> IO ()
    aux name =
      case Map.lookup name decls of
        Just (DTypeDef typeDef) -> declareDatatype solver name typeDef
        _ -> return ()

-- | Initialize a solver and declare datatypes from Pirouette definitions
smtMain :: PrtOrderedDefs -> IO ()
smtMain decls = do
  s <- prepareSMT
  declareDatatypes s decls

-- | Constraints on names and builtins to translate Pirouette datatypes
type TranslationConstraints name builtins =
  (Show name, Show builtins, Translatable builtins)

instance Show name => Translatable (TypeBase name) where
  translate (TyBuiltin pirType) = translate pirType
  translate (TyFree name) = SmtLib.symbol (toSmtName name)

instance Translatable PIRType where
  translate PIRTypeInteger = SmtLib.tInt
  translate PIRTypeBool = SmtLib.tBool
  translate PIRTypeString = SmtLib.tString
  translate PIRTypeUnit = SmtLib.tUnit
  -- Note: why do Pair have maybes?
  translate (PIRTypePair (Just pirType1) (Just pirType2)) =
    SmtLib.tTuple [translate pirType1, translate pirType2]
  translate pirType =
    error $ "Translate builtin type to smtlib: " <> show pirType <> " not yet handled."

instance TranslationConstraints name builtins => Translatable (AnnType name (Var name builtins)) where
  translate (TyApp (F ty) args) = SmtLib.app (translate ty) (map translate args)
  translate (TyApp (B (Ann ann) index) args) =
    SmtLib.app (SmtLib.symbol (toSmtName ann)) (map translate args)
  translate x = error $ "Translate type to smtlib: cannot handle " <> show x
