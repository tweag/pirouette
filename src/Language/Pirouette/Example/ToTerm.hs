{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

-- | Provides a simple translation from the syntactical categories
--  of "Language.Pirouette.Example.Syntax" into their respective
--  counterparts in "Pirouette.Term.Base". The main aspect of this
--  translation is computing de Bruijn indices.
module Language.Pirouette.Example.ToTerm where

import Control.Arrow (first)
import Control.Monad.Except
import Data.List (elemIndex, nub, (\\))
import qualified Data.Map as M
import Data.String
import Language.Pirouette.Example.Syntax
import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as SystF

type TrM = Except String

type Env = [String]

trProgram ::
  M.Map String (Either DataDecl FunDecl) ->
  FunDecl ->
  TrM (M.Map Name (Definition Ex), Definition Ex)
trProgram env main@FunDecl {} =
  let decls =
        mapM (uncurry (\s -> either (trDataDecl s) (fmap ((: []) . (fromString s,)) . trFunDecl))) $
          M.toList env
   in (,) <$> (decls >>= toDecls . concat) <*> trFunDecl main
  where
    toDecls :: [(Name, Definition Ex)] -> TrM (Decls Ex)
    toDecls ds =
      let names = map fst ds
          repeated = names \\ nub names
       in if null repeated
            then return $ M.fromList ds
            else throwError $ "Repeaded definitions: " ++ show repeated

trFunDecl :: FunDecl -> TrM (Definition Ex)
trFunDecl (FunDecl rec ty expr) =
  DFunDef <$> (FunDef rec <$> trTerm [] [] expr <*> trType [] ty)

trDataDecl :: String -> DataDecl -> TrM [(Name, Definition Ex)]
trDataDecl sName (DataDecl vars cons) = do
  let ki = foldr (SystF.KTo . snd) SystF.KStar vars
  let name = fromString sName
  let destName = fromString $ "match_" ++ sName
  constrs <- mapM (\(n, ty) -> (fromString n,) <$> trTypeWithEnv (reverse vars) ty) cons
  return $
    (name, DTypeDef $ Datatype ki (map (first fromString) vars) destName constrs) :
    (destName, DDestructor name) :
    zipWith (\n i -> (fst n, DConstructor i name)) constrs [0 ..]

trTypeWithEnv :: [(String, SystF.Kind)] -> Ty -> TrM (Type Ex)
trTypeWithEnv env ty = do
  ty' <- trType (map fst env) ty
  return $ foldr (\(s, ki) -> SystF.TyAll (SystF.Ann $ fromString s) ki) ty' env

trType :: Env -> Ty -> TrM (Type Ex)
trType env (TyLam s ki ty) = SystF.TyLam (SystF.Ann $ fromString s) ki <$> trType (s : env) ty
trType env (TyAll s ki ty) = SystF.TyAll (SystF.Ann $ fromString s) ki <$> trType (s : env) ty
trType env (TyFun ty ty2) = SystF.TyFun <$> trType env ty <*> trType env ty2
trType env (TyApp ty ty2) = SystF.app <$> trType env ty <*> trType env ty2
trType env (TyVar s) =
  case s `elemIndex` env of
    Just i -> return $ SystF.tyPure $ SystF.Bound (SystF.Ann $ fromString s) (fromIntegral i)
    Nothing -> throwError $ "type variable " ++ s ++ " undeclared"
trType _ (TyFree s) = return $ SystF.tyPure $ SystF.Free $ TySig (fromString s)
trType _ (TyBase et) = return $ SystF.tyPure $ SystF.Free $ TyBuiltin et

trTerm :: Env -> Env -> Expr -> TrM (Term Ex)
trTerm tyEnv termEnv (ExprApp ex (ExprTy tyArg)) =
  SystF.app <$> trTerm tyEnv termEnv ex <*> (SystF.TyArg <$> trType tyEnv tyArg)
trTerm tyEnv termEnv (ExprApp ex arg) =
  SystF.app <$> trTerm tyEnv termEnv ex <*> (SystF.TermArg <$> trTerm tyEnv termEnv arg)
trTerm _ _ (ExprTy _) = throwError "ExprTy found outside an ExprApp chain"
trTerm tyEnv termEnv (ExprLam s ty ex) =
  SystF.Lam (SystF.Ann $ fromString s) <$> trType tyEnv ty <*> trTerm tyEnv (s : termEnv) ex
trTerm tyEnv termEnv (ExprAbs s ki ex) =
  SystF.Abs (SystF.Ann $ fromString s) ki <$> trTerm (s : tyEnv) termEnv ex
trTerm tyEnv termEnv (ExprIf ty c t e) = do
  ty' <- trType tyEnv ty
  c' <- trTerm tyEnv termEnv c
  t' <- trTerm tyEnv termEnv t
  e' <- trTerm tyEnv termEnv e
  return $ SystF.App (SystF.Free $ Builtin TermIte) $ SystF.TyArg ty' : map SystF.TermArg [c', t', e']
trTerm _ termEnv (ExprVar s) =
  case s `elemIndex` termEnv of
    Just i -> return $ SystF.termPure $ SystF.Bound (SystF.Ann $ fromString s) (fromIntegral i)
    Nothing -> return $ SystF.termPure $ SystF.Free $ TermSig (fromString s)
trTerm _ _ (ExprLit ec) = return $ SystF.termPure (SystF.Free $ Constant ec)
trTerm _ _ (ExprBase et) = return $ SystF.termPure (SystF.Free $ Builtin et)
