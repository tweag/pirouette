{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Translation of datatype declarations and type terms from
-- PlutusIR/Pirouette to smtlib through the SimpleSMT library.
module Pirouette.SMT.Datatypes where

import Control.Monad.IO.Class
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Debug.Trace
import Pirouette.Monad
import Pirouette.SMT.Common
import qualified Pirouette.SMT.SimpleSMT as SmtLib
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base
import Pirouette.Term.Syntax.SystemF
import Pirouette.Term.FromPlutusIR

-- | Declare a datatype in the solver
declareDatatype :: MonadIO m => SmtLib.Solver -> Name -> TypeDef PlutusIR Name -> m ()
declareDatatype solver typeName typeDef@(Datatype _ typeVariabes _ constructors) =
  liftIO $
    SmtLib.declareDatatype
      solver
      (toSmtName typeName)
      (map (toSmtName . fst) typeVariabes)
      (constructorFromPIR <$> constructors)

-- | The definition of constructors in SMTlib follows a fixed layout. This
-- function translates constructor types in PlutusIR to this layout and
-- provides required names for the fields of product types.
constructorFromPIR ::
  forall builtins.
  TranslationConstraints builtins =>
  (Name, AnnType Name (Var Name builtins)) ->
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
    aux :: AnnType Name (Var Name builtins) -> [SmtLib.SExpr]
    aux x = let (args, _) = tyFunArgs x in map translate args

-- Declare all the datatypes in the solver from an ordered set of Pirouette
-- definitions
declareDatatypes ::
  MonadIO m => SmtLib.Solver -> Map Name (PrtDef PlutusIR) -> [Arg Name Name] -> m ()
declareDatatypes solver decls orderedNames =
  let typeNames =
        mapMaybe
          (\case (TyArg name) -> Just name; _ -> Nothing)
          orderedNames
   in mapM_ aux typeNames
  where
    aux :: MonadIO m => Name -> m ()
    aux name =
      -- We tried to blacklist types with higher order constructor parameters
      -- But these are required further down so it is not a solution
      -- show name == "Monoid" = return () -- XXX DEBUG
      -- show name == "AdditiveMonoid" = return () -- XXX DEBUG
      -- otherwise =
      trace (show name) $
        case Map.lookup name decls of
          Just (DTypeDef typeDef) -> declareDatatype solver name typeDef
          _ -> return ()

-- | Initialize a solver and declare datatypes from Pirouette definitions
smtMain :: PrtOrderedDefs PlutusIR -> IO ()
smtMain PrtOrderedDefs {prtDecls = decls, prtDepOrder = orderedNames} = do
  s <- prepareSMT
  declareDatatypes s decls orderedNames

-- | Constraints on names and builtins to translate Pirouette datatypes
type TranslationConstraints builtins =
  (Show builtins, Translatable builtins)

instance Translatable (TypeBase PlutusIR Name) where
  translate (TyBuiltin pirType) = translate pirType
  translate (TyFree name) = SmtLib.symbol (toSmtName name)

instance Translatable PIRType where
  translate PIRTypeInteger = SmtLib.tInt
  translate PIRTypeBool = SmtLib.tBool
  translate PIRTypeString = SmtLib.tString
  translate PIRTypeByteString = SmtLib.tString
  translate PIRTypeUnit = SmtLib.tUnit
  translate PIRTypeData = SmtLib.tUnit -- TODO: Temporary represention of data
  -- Note: why do Pair have maybes?
  -- Note answer, because types can be partially applied in System F,
  -- and `Pair a` is represented by `PIRTypePair (pirType a) Nothing`
  translate (PIRTypePair (Just pirType1) (Just pirType2)) =
    SmtLib.tTuple [translate pirType1, translate pirType2]
  translate pirType =
    error $ "Translate builtin type to smtlib: " <> show pirType <> " not yet handled."

instance TranslationConstraints builtins => Translatable (AnnType Name (Var Name builtins)) where
  translate (TyApp (F ty) args) = SmtLib.app (translate ty) (map translate args)
  translate (TyApp (B (Ann ann) index) args) =
    SmtLib.app (SmtLib.symbol (toSmtName ann)) (map translate args)
  translate x = error $ "Translate type to smtlib: cannot handle " <> show x
