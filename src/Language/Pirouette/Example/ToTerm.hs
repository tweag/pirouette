{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
module Language.Pirouette.Example.ToTerm where

import Data.Data
import Pirouette.Term.Builtins
import Pirouette.Term.Syntax.Base
import Language.Pirouette.Example.Syntax
import Control.Monad.Except
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Data.String
import Data.List (elemIndex)
import qualified Data.Map as M

data Ex deriving Data
instance LanguageBuiltins Ex where
  type BuiltinTypes Ex = ExTypes
  type BuiltinTerms Ex = ExTerm
  type Constants Ex = ExConstant

type TrM = Except String

type Env = [String]

trProgram :: M.Map String (Either DataDecl FunDecl) -> FunDecl
          -> TrM (M.Map Name (Definition Ex), Term Ex)
trProgram env (FunDecl _ main) =
  let decls = mapM (uncurry (\s -> either (trDataDecl s) (fmap ((:[]) . (fromString s,)) . trFunDecl))) $ M.toList env
   in (,) <$> (M.fromList . concat <$> decls) <*> trTerm [] [] main

trFunDecl :: FunDecl -> TrM (Definition Ex)
trFunDecl (FunDecl ty expr) =
  DFunDef <$> (FunDef Rec <$> trTerm [] [] expr <*> trType [] ty)

trDataDecl :: String -> DataDecl -> TrM [(Name, Definition Ex)]
trDataDecl sName (DataDecl vars cons) = do
  let (vNames, vKinds) = unzip vars
  let ki = foldr SystF.KTo SystF.KStar vKinds
  let tyEnv = reverse vNames
  let name = fromString sName
  let destName = fromString $ "match_" ++ sName
  constrs <- mapM (\(n, ty) -> (fromString n ,) <$> trType tyEnv ty) cons
  return
    $ (name, DTypeDef $ Datatype ki undefined destName constrs)
    : (destName, DDestructor name)
    : zipWith (\n i -> (fst n, DConstructor i name)) constrs [0..]

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

trTerm :: Env -> Env -> Expr -> TrM (Term Ex)
trTerm tyEnv termEnv (ExprApp ex (ExprTy tyArg)) =
  SystF.app <$> trTerm tyEnv termEnv ex <*> (SystF.TyArg <$> trType tyEnv tyArg)
trTerm tyEnv termEnv (ExprApp ex arg) =
  SystF.app <$> trTerm tyEnv termEnv ex <*> (SystF.TermArg <$> trTerm tyEnv termEnv arg)
trTerm tyEnv termEnv (ExprTy ty) = throwError "ExprTy found outside an ExprApp chain"
trTerm tyEnv termEnv (ExprLam s ty ex) =
  SystF.Lam (SystF.Ann $ fromString s) <$> trType tyEnv ty <*> trTerm tyEnv (s:termEnv) ex
trTerm tyEnv termEnv (ExprAbs s ki ex) =
  SystF.Abs (SystF.Ann $ fromString s) ki <$> trTerm (s:tyEnv) termEnv ex
trTerm tyEnv termEnv (ExprIf c t e) = do
  c' <- trTerm tyEnv termEnv c
  t' <- trTerm tyEnv termEnv t
  e' <- trTerm tyEnv termEnv e
  return $ SystF.App (SystF.Free $ Builtin TermIte) $ map SystF.TermArg [c', t', e']
trTerm tyEnv termEnv (ExprVar s) =
  case s `elemIndex` termEnv of
    Just i -> return $ SystF.termPure $ SystF.Bound (SystF.Ann $ fromString s) (fromIntegral i)
    Nothing -> throwError $ "Variable " ++ s ++ " undeclared"
trTerm tyEnv termEnv (ExprLit ec) = return $ SystF.termPure (SystF.Free $ Constant ec)
trTerm tyEnv termEnv (ExprBase et) = return $ SystF.termPure (SystF.Free $ Builtin et)
