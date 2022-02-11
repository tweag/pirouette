{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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

-- | Declare a datatype in the solver
declareDatatype :: (LanguageSMT lang, MonadIO m) => SmtLib.Solver -> Name -> TypeDef lang Name -> m ()
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
  forall lang meta .
  (LanguageSMT lang, ToSMT meta) =>
  (Name, PrtTypeMeta lang meta) ->
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
    aux :: PrtTypeMeta lang meta -> [SmtLib.SExpr]
    aux x = let (args, _) = tyFunArgs x in map translateType args

-- Declare all the datatypes in the solver from an ordered set of Pirouette
-- definitions
declareDatatypes ::
  (LanguageSMT lang, MonadIO m) => SmtLib.Solver -> Map Name (PrtDef lang) -> [Arg Name Name] -> m ()
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

translateTypeBase :: forall lang . (LanguageSMT lang) => TypeBase lang Name -> SmtLib.SExpr
translateTypeBase (TyBuiltin pirType) = translateBuiltinType @lang pirType
translateTypeBase (TyFree name) = SmtLib.symbol (toSmtName name)

translateType :: (LanguageSMT lang, ToSMT meta) => PrtTypeMeta lang meta -> SmtLib.SExpr
translateType (TyApp (F ty) args) = SmtLib.app (translateTypeBase ty) (map translateType args)
translateType (TyApp (B (Ann ann) index) args) =
  SmtLib.app (SmtLib.symbol (toSmtName ann)) (map translateType args)
translateType x = error $ "Translate type to smtlib: cannot handle " <> show x

-- | Initialize a solver and declare datatypes from Pirouette definitions
smtMain :: (LanguageSMT lang) => PrtOrderedDefs lang -> IO ()
smtMain PrtOrderedDefs {prtDecls = decls, prtDepOrder = orderedNames} = do
  s <- prepareSMT
  declareDatatypes s decls orderedNames
