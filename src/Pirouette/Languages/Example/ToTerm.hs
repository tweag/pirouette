{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Pirouette.Languages.Example.ToTerm where

import Data.Data
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax.Base
import Pirouette.Languages.Example.Syntax
import Control.Monad.Except
import Control.Monad.Reader
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Data.String
import Data.List (elemIndex)

data Ex deriving Data
instance LanguageBuiltins Ex where
  type BuiltinTypes Ex = ExTypes
  type BuiltinTerms Ex = ExTerm
  type Constants Ex = ExConstant

type TrM = Except String

type Env = [String]

trFunDecl :: FunDecl -> TrM (Name, Definition Ex)
trFunDecl = undefined

trDataDecl :: DataDecl -> TrM [(Name, Definition Ex)]
trDataDecl = undefined

trType :: Env -> Ty -> TrM (Type Ex)
trType env (TyLam s ki ty) = SystF.TyLam (SystF.Ann $ fromString s) ki <$> trType (s:env) ty
trType env (TyAll s ki ty) = SystF.TyAll (SystF.Ann $ fromString s) ki <$> trType (s:env) ty
trType env (TyFun ty ty2) = SystF.TyFun <$> trType env ty <*> trType env ty2
trType env (TyApp ty ty2) = SystF.app <$> trType env ty <*> trType env ty2
trType env (TyVar s) =
  case s `elemIndex` env of
    Just i -> return $ SystF.tyPure $ SystF.Bound (SystF.Ann $ fromString s) (fromIntegral i)
    Nothing -> throwError $ "Variable " ++ s ++ " undeclared"
trType env (TyFree s) = return $ SystF.tyPure $ SystF.Free $ TySig (fromString s)
trType env (TyBase et) = return $ SystF.tyPure $ SystF.Free $ TyBuiltin et

trExpr :: Env -> Expr -> TrM (Term Ex)
trExpr = undefined
