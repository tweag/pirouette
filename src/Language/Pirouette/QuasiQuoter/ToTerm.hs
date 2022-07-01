{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

-- | Provides a simple translation from the syntactical categories
--  of "Language.Pirouette.QuasiQuoter.Syntax" into their respective
--  counterparts in "Pirouette.Term.Base". The main aspect of this
--  translation is computing de Bruijn indices.
module Language.Pirouette.QuasiQuoter.ToTerm where

import Control.Arrow (first)
import Control.Monad.Except
import Data.List (elemIndex, nub, (\\))
import qualified Data.Map as M
import Data.String
import Language.Pirouette.QuasiQuoter.Syntax
import Pirouette.Term.Syntax.Base
import qualified Pirouette.Term.Syntax.SystemF as SystF

type TrM = Except String

type Env = [String]

trProgram ::
  (LanguageParser lang) =>
  M.Map String (Either (DataDecl lang) (FunDecl lang)) ->
  TrM (M.Map (Namespace, Name) (Definition lang))
trProgram env =
  let decls = forM (M.toList env) $ \case
        (s, Left td) -> trDataDecl s td
        (s, Right f) -> (\r -> [((TermNamespace, fromString s), r)]) <$> trFunDecl f
   in decls >>= toDecls . concat
  where
    toDecls :: [((Namespace, Name), Definition lang)] -> TrM (Decls lang)
    toDecls ds =
      let names = map fst ds
          repeated = names \\ nub names
       in if null repeated
            then return $ M.fromList ds
            else throwError $ "Repeaded definitions: " ++ show repeated

trFunDecl :: (LanguageParser lang) => FunDecl lang -> TrM (Definition lang)
trFunDecl (FunDecl rec ty expr) =
  DFunDef <$> (FunDef rec <$> trTerm [] [] expr <*> trType [] ty)

trDataDecl :: String -> DataDecl lang -> TrM [((Namespace, Name), Definition lang)]
trDataDecl sName (DataDecl vars cons) = do
  let ki = foldr (SystF.KTo . snd) SystF.KStar vars
  let name = fromString sName
  let destName = fromString $ "match_" ++ sName
  constrs <- mapM (\(n, ty) -> (fromString n,) <$> trTypeWithEnv (reverse vars) ty) cons
  return $
    ((TypeNamespace, name), DTypeDef $ Datatype ki (map (first fromString) vars) destName constrs) :
    ((TermNamespace, destName), DDestructor name) :
    zipWith (\n i -> ((TermNamespace, fst n), DConstructor i name)) constrs [0 ..]

trTypeWithEnv :: [(String, SystF.Kind)] -> Ty lang -> TrM (Type lang)
trTypeWithEnv env ty = do
  ty' <- trType (map fst env) ty
  return $ foldr (\(s, ki) -> SystF.TyAll (SystF.Ann $ fromString s) ki) ty' env

trType :: Env -> Ty lang -> TrM (Type lang)
trType env (TyLam s ki ty) = SystF.TyLam (SystF.Ann $ fromString s) ki <$> trType (s : env) ty
trType env (TyAll s ki ty) = SystF.TyAll (SystF.Ann $ fromString s) ki <$> trType (s : env) ty
trType env (TyFun ty ty2) = SystF.TyFun <$> trType env ty <*> trType env ty2
trType env (TyApp ty ty2) = SystF.app <$> trType env ty <*> trType env ty2
trType env (TyVar s) =
  case s `elemIndex` env of
    Just i -> return $ SystF.TyPure $ SystF.Bound (SystF.Ann $ fromString s) (fromIntegral i)
    Nothing -> throwError $ "type variable " ++ s ++ " undeclared"
trType _ (TyFree s) = return $ SystF.TyPure $ SystF.Free $ TySig (fromString s)
trType _ (TyBase et) = return $ SystF.TyPure $ SystF.Free $ TyBuiltin et

trTerm :: (LanguageParser lang) => Env -> Env -> Expr lang -> TrM (Term lang)
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
  return $ ifThenElse ty' c' t' e'
trTerm _ termEnv (ExprVar s) =
  case s `elemIndex` termEnv of
    Just i -> return $ SystF.termPure $ SystF.Bound (SystF.Ann $ fromString s) (fromIntegral i)
    Nothing -> return $ SystF.termPure $ SystF.Free $ TermSig (fromString s)
trTerm _ _ (ExprLit ec) = return $ SystF.termPure (SystF.Free $ Constant ec)
trTerm _ _ (ExprBase et) = return $ SystF.termPure (SystF.Free $ Builtin et)
