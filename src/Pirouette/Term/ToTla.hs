{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deferred-type-errors #-}
module Pirouette.Term.ToTla where

import           Pirouette.Monad
import           Pirouette.Monad.Maybe
import           Pirouette.Monad.Logger
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax
import           Pirouette.Term.ConstraintTree
import           Pirouette.Term.Transformations
import           Pirouette.PlutusIR.Utils
import           Pirouette.TLA.Syntax
import           Pirouette.TLA.Type
import           Pirouette.Specializer

import qualified PlutusCore as P

import qualified Language.TLAPlus.Syntax as TLA
import qualified Language.TLAPlus.Parser as TLA
import qualified Text.ParserCombinators.Parsec     as P

import           Control.Applicative hiding (empty)
import           Control.Monad.Reader
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Arrow (first, second, (***))

import           Data.Functor ( ($>) )
import           Data.Maybe ( mapMaybe, isJust, catMaybes )
import           Data.Generics.Uniplate.Operations
import           Data.String
import           Data.Bifunctor (bimap)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.List as L

import qualified Language.TLAPlus.Pretty as TLA

-- * TLA Splicing

-- |Splices expressions
newtype TLAExprWrapper = TLAExprWrapper { wrapExp :: TLA.AS_Expression -> TLA.AS_Expression }

-- |Given a string which parses as a TLA expression @E@, produces a wrapper that
-- given another expression @x@, substitutes @tlaIdent "___"@ for @x@ in @E@.
mkTLAExprWrapper :: (MonadPirouette m) => String -> m TLAExprWrapper
mkTLAExprWrapper exp =
  case P.runParser TLA.expression TLA.mkState "mkTLAExprWrapper" exp of
    Left err   -> pushCtx "mkTLAExprWrapper" $
      fail $ "Error with " ++ exp ++ "\n " ++ show err
    Right expr -> return $ TLAExprWrapper $ \e -> rewrite (go e) expr
  where
    go e (TLA.AS_Ident _ [] "___") = Just e
    go _ _                         = Nothing


-- |Splices definitions within a module
newtype TLASpecWrapper = TLASpecWrapper { wrapSpec :: [TLA.AS_UnitDef] -> TLA.AS_Spec }

-- |Given a TLA Spec, creates a 'TLASpecWrapper' that will inject its provided definitions
-- after the first 'TLA.AS_Separator' it sees. A separator is a line containing only, but at
-- least four, '-' characters.
mkTLASpecWrapper :: (MonadPirouette m) => String -> m TLASpecWrapper
mkTLASpecWrapper exp =
  case P.runParser TLA.tlaspec TLA.mkState "mkTLASpecWrapper" exp of
    Left err   -> pushCtx "mkTLASpecWrapper" $ fail $ show err
    Right spec -> return $ TLASpecWrapper $ \e -> spec { TLA.unitDef = expand (TLA.unitDef spec) e }
  where
    expand [] _ = []
    expand (TLA.AS_Separator d : us) e = TLA.AS_Separator d : e ++ us
    expand (u                  : us) e = u : expand us e

mkTLATySpecializer :: [String] -> String -> Maybe TypeSpecializer
mkTLATySpecializer ["ALL"] s = allSpz s
mkTLATySpecializer l       s =
  if elem s l then allSpz s else Nothing

-- * TLA AST Example
--
-- $tlaastexample
--
-- As an example, parsing the following TLA file:
--
-- > ---- MODULE Test ----
-- >
-- > EXTENDS FinSeq
-- >
-- > Apply(f(_,_), x, y) == f(x, y)
-- >
-- > Pick(S) == CHOOSE s \in S : TRUE
-- > RECURSIVE SetReduce(_, _, _)
-- > SetReduce(Op(_, _), S, value) == IF S = {} THEN value
-- >                               ELSE LET s == Pick(S)
-- >                               IN SetReduce(Op, S \ {s}, Op(s, value))
-- >
-- > WrappedAction == \E m \in TypeM \X N, x \in TypeX : Action(m,x)
-- > Action(m,x) == /\ doM1(m,n)
-- >                /\ s' = 3
-- >
-- > =====================
--
-- Yields the following AST, with source position information removed for clarity:
--
-- > AS_Spec {
-- >   Name       = "Test",
-- >   extendDecl = AS_ExtendDecl ["FinSeq"],
-- >   unitDef    = [ AS_OperatorDef False
-- >                    (AS_OpHead (AS_Ident  [] "Apply")
-- >                               [ AS_OpApp (AS_Ident  [] "f") [AS_Ident  [] "_",AS_Ident  [] "_"]
-- >                               , AS_Ident [] "x"
-- >                               , AS_Ident [] "y"])
-- >                    (AS_OpApp  (AS_Ident  [] "f") [AS_Ident  [] "x",AS_Ident  [] "y"])
-- >                , AS_OperatorDef False
-- >                    (AS_OpHead (AS_Ident [] "Pick") [AS_Ident [] "S"])
-- >                    (AS_Choose (AS_QBound1 (AS_Ident [] "s") (AS_Ident [] "S")) (AS_Bool True))
-- >                , AS_RecursiveDecl [AS_OpHead (AS_Ident  [] "SetReduce") [AS_Ident  [] "_",AS_Ident  [] "_",AS_Ident  [] "_"]]
-- >                , AS_OperatorDef False
-- >                    (AS_OpHead (AS_Ident [] "SetReduce")
-- >                               [AS_OpApp (AS_Ident  [] "Op") [AS_Ident  [] "_",AS_Ident  [] "_"]
-- >                               , AS_Ident [] "S"
-- >                               , AS_Ident [] "value"])
-- >                    (AS_IF (AS_InfixOP  AS_EQ (AS_Ident  [] "S") (AS_DiscreteSet  []))
-- >                           (AS_Ident [] "value")
-- >                           (AS_Let [AS_OperatorDef False (AS_OpHead (AS_Ident  [] "s") [])
-- >                                        (AS_OpApp  (AS_Ident  [] "Pick") [AS_Ident  [] "S"])]
-- >                                   (AS_OpApp ( AS_Ident  [] "SetReduce")
-- >                                             [ AS_Ident  [] "Op"
-- >                                             , AS_InfixOP  AS_SetMinus (AS_Ident  [] "S") (AS_DiscreteSet  [AS_Ident  [] "s"])
-- >                                             , AS_OpApp  (AS_Ident  [] "Op") [AS_Ident  [] "s",AS_Ident  [] "value"]])))
-- >                , AS_OperatorDef False
-- >                    (AS_OpHead (AS_Ident  [] "WrappedAction") [])
-- >                    (AS_Quantified  AS_Exist
-- >                       [AS_QBoundN [AS_Ident [] "m"] (AS_InfixOP  AS_Times (AS_Ident  [] "TypeM") (AS_Ident  [] "N"))
-- >                       ,AS_QBoundM [AS_Ident [] "x"  (AS_Ident [] "TypeX")]
-- >                       (AS_OpApp  (AS_Ident  [] "Action") [AS_Ident  [] "m", AS_Ident [] "x"]))
-- >                , AS_OperatorDef False
-- >                    (AS_OpHead (AS_Ident  [] "Action") [AS_Ident  [] "m", AS_Ident [] "x"])
-- >                    (AS_LAND  [ AS_OpApp  (AS_Ident  [] "doM1") [AS_Ident  [] "m", AS_Ident [] "x"]
-- >                              , AS_InfixOP  AS_EQ (AS_PostfixOP  AS_Prime (AS_Ident  [] "s")) (AS_Num  3)])
-- >                ]}

-- * Translating PrtTerm to TLA

-- ** TLA Translation Monad

type TlaT m = ReaderT TlaOpts (StateT TlaState m)

tlaPure :: (Monad m) => m a -> TlaT m a
tlaPure = lift . lift

tlaPushCtx :: (MonadLogger m) => String -> TlaT m a -> TlaT m a
tlaPushCtx ctx = mapReaderT (mapStateT $ pushCtx ctx)

data TlaOpts = TlaOpts
  { toSymbExecOpts  :: CTreeOpts
  , toActionWrapper :: TLAExprWrapper
  , toSkeleton      :: TLASpecWrapper
  , toSpecialize    :: String -> Maybe TypeSpecializer
  }

data TlaState = TlaState
  { tsFreshNameCtr :: Int
  , tsTyVars       :: [(Name, R.Kind)]
  , tsTypeOf       :: M.Map TLA.AS_Expression TlaType
  , tsSubst        :: M.Map Name TLA.AS_Expression
  }

tsRegisterSubst :: (Monad m) => Name -> TLA.AS_Expression -> TlaT m ()
tsRegisterSubst n term = modify (\st -> st{ tsSubst = M.insert n term (tsSubst st) })

tlaState0 :: TlaState
tlaState0 = TlaState 0 [] M.empty M.empty

tlaFreshNameStr :: (Monad m) => TlaT m String
tlaFreshNameStr = do
  c <- gets tsFreshNameCtr
  modify (\st -> st { tsFreshNameCtr = c + 1 })
  return $ "fn" ++ show c

tlaFreshName :: (Monad m) => TlaT m TLA.AS_Expression
tlaFreshName = tlaIdent <$> tlaFreshNameStr

tlaDeclTypeOf :: (MonadPirouette m) => TLA.AS_Expression -> TlaType -> TlaT m ()
tlaDeclTypeOf n ty = tlaPushCtx "tlaDeclTypeOf" $ do
  tlaPure $ logTrace $ showId n ++ ": " ++ renderSingleLineStr (pretty ty)
  modify (\st -> st { tsTypeOf = M.insert n ty (tsTypeOf st) })
  where
    showId (TLA.AS_Ident _ _ x) = x

tlaWithDeclTypeOf :: (MonadPirouette m) => [(TLA.AS_Expression, TlaType)] -> TlaT m a -> TlaT m a
tlaWithDeclTypeOf ntys f = do
  pre <- gets tsTypeOf
  modify (\st -> st { tsTypeOf = M.fromList ntys `M.union` pre })
  res <- f
  modify (\st -> st { tsTypeOf = pre })
  return res


tlaWithTyVars :: (Monad m) => [(Name, R.Kind)] -> TlaT m a -> TlaT m a
tlaWithTyVars tyvs f = do
  pre <- gets tsTyVars
  modify (\st -> st { tsTyVars = reverse tyvs ++ pre })
  res <- f
  modify (\st -> st { tsTyVars = pre })
  return res

-- ** Top-Level Translation

-- |Translates a term to a TLA specification by first symbolically executing the term
-- then translating the necessary parts. We also receive a list of names that specify the
-- order in which they must be defined. This list can be obtained from 'elimEvenOddMutRec'
termToSpec :: (MonadPirouette m)
           => TlaOpts -> Name -> PrtTerm
           -> m TLA.AS_Spec
termToSpec opts mainFun t = flip evalStateT tlaState0 $ flip runReaderT opts $ do
  tlaPure $ logDebug "Translating Dependencies"
  depsMain   <- tlaPure $ transitiveDepsOf mainFun
  sortedDeps <- tlaPure dependencyOrder
  let neededDeps = filter (`S.member` depsMain) sortedDeps
  deps <- mapM (R.argElim (trTypeName opts) trTermName) neededDeps

  tlaPure $ logDebug $ "Symbolically executing " ++ show mainFun
  mctree <- tlaPure $ termToCTree (toSymbExecOpts opts) mainFun t
  tlaPure $ logDebug $ "Translating Action Definitions for " ++ show mainFun
  defs   <- case mctree of
    Choose x ty br -> concatMap p2l <$> mapM (uncurry $ matchToAction x ty) br
    Result t       -> tlaPure (logDebug ("tree: " ++ show (pretty t)))
                        >> throwError' (PEOther "CTreeIsNotAMatch")
  let next = tlaOpDef (tlaIdent "Next") [] $ tlaOr $ map (tlaIdentPrefixed "Wrapped") $ ctreeFirstMatches mctree

  tlaPure $ logDebug "Assembling the spec"
  skel <- asks toSkeleton
  return $ wrapSpec skel
         $ concat deps ++ defs ++ [next]
  where
    p2l (x, y) = [x, y]

trTypeName :: (MonadPirouette m) => TlaOpts -> Name -> TlaT m [TLA.AS_UnitDef]
trTypeName opts n = do
  tyDef <- tlaPure (typeDefOf n)
  decl <- trTypeDecl n tyDef
  case toSpecialize opts (T.unpack $ nameString n) of
    Nothing -> return decl
    Just (TypeSpecializer set c dest _) ->
      return $ set : dest : c


trTermName :: (MonadPirouette m) => Name -> TlaT m [TLA.AS_UnitDef]
trTermName n = tlaPushCtx (show n) $ tlaPushCtx "trTermName" $ do
  defN <- tlaPure $ defOf n
  case defN of
    DFunction _ t ty -> do
      let tlaTy = toTlaOpType ty
      tlaDeclTypeOf (tlaIdent n) tlaTy
      concatMap (\(x,y) -> [x,y]) <$> trTermNameRec n
    _ -> return []

trTermNameRec :: (MonadPirouette m) => Name -> TlaT m [(TLA.AS_UnitDef, TLA.AS_UnitDef)]
trTermNameRec n = do
  defN <- tlaPure $ defOf n
  case defN of
    DFunction _ t ty -> do
      tlaTy <- tlaTypeOfName n
      (:[]) <$> trTermDecl n t tlaTy
    _ -> return []

trTermDecl :: (MonadPirouette m) => Name -> PrtTerm -> TlaType -> TlaT m (TLA.AS_UnitDef, TLA.AS_UnitDef)
trTermDecl n term tlaTy = do
  let (tyargs, term') = R.getHeadAbs term
  let (args,   body)  = R.getHeadLams term'
  let hd    =  TLA.AS_OpHead (tlaIdent n) $ map (uncurry extractVars) args
  let hdAn  =  TLA.AS_OpHead (tlaIdent n) $ map (const $ tlaIdent "_") args
  let dec   = TLA.AS_RecursiveDecl diu [hdAn]
  def <- tlaWithDeclTypeOf (map (uncurry declArgs) args)
       $ tlaWithTyVars tyargs
       $ TLA.AS_OperatorDef diu False hd <$> trTerm body (TlaVal $ returnType tlaTy)
  return (dec, def)
  where
    funToUnderscores :: PrtType -> [TLA.AS_Expression]
    funToUnderscores t = map (const $ tlaIdent "_") . fst $ R.tyFunArgs t

    declArgs :: Name -> PrtType -> (TLA.AS_Expression, TlaType)
    declArgs n ty = (tlaIdent n, toTlaOpType ty)

    extractVars :: Name -> PrtType -> TLA.AS_Expression
    extractVars n ty =
      let i = R.tyMonoArity ty in
      if i == 0
      then tlaIdent n
      else
        tlaOpApp (tlaIdent n) (replicate i (tlaIdent "_"))

declareTermNameMutRec :: (MonadPirouette m) => Name -> TlaT m ()
declareTermNameMutRec n = do
  defN <- tlaPure $ defOf n
  case defN of
    -- When functions are mutually recursive, they cannot be declared higher-order,
    -- so their type is declared using `toTlaHdOpType` rather than the
    -- usual `toTlaOpType`.
    DFunction _ t ty -> tlaDeclTypeOf (tlaIdent n) (toTlaHdOpType ty)
    _                -> return ()

-- |Given a ctree that starts with a match over a variable, for example,
--
-- >  (Match i#0 with Dec m) :&: rest
--
-- Yields two TLA actions, one which receives "m" as a parameter and a wrapped one,
-- with no parameters:
--
-- > Dec(m)     == trTree (rest [ i := Dec m ])
-- > WrappedDec == \E m \in TypeM : Dec(m)
matchToAction :: (MonadPirouette m)
              => PrtTerm -> PrtType -> Constraint Name -> CTree Name
              -> TlaT m (TLA.AS_UnitDef, TLA.AS_UnitDef)
matchToAction val ty (Match cons args) rest =
  case val of
    R.App (R.B (R.Ann valN) _) [] -> do
      let argIds = map (tlaIdent . fst) args
      consExpr <- trConstrApp cons argIds
      tsRegisterSubst valN consExpr
      rest' <- tlaWithDeclTypeOf (map (tlaIdent *** TlaVal) args)
             $ trTree rest ty
      let op            = tlaOpDef (tlaIdentPrefixed "Action" cons) argIds rest'
      let opWrap body   = tlaAssign (tlaIdentPrefixed "Wrapped" cons) body
      let opWrapBody qb = (if null qb then id else TLA.AS_Quantified di TLA.AS_Exist qb)
                        $ tlaOpApp (tlaIdentPrefixed "Action" cons) argIds
      qboundNs <- mapM (uncurry trQBoundN) args
      return (op, opWrap (opWrapBody qboundNs))
    _                     -> throwError' $ PEOther "MatchIsNotAVariable"

-- *** Translating Types

trTypeDecl :: (MonadPirouette m)
            => Name -> PrtTypeDef -> TlaT m [TLA.AS_UnitDef]
trTypeDecl tyName (Datatype _ tyVars destr constr) = do
  constr' <- mapM (uncurry (trConstrDecl tyVars)) constr
  destr'  <- trDestrDecl tyVars destr constr tyName
  bset    <- trBoundedSetDef tyName tyVars constr
  return (destr' : constr' ++ bset)

-- |Given a datatype @data XXX a b = A a | B b (XXX a b) | C (XXX a b)@, calling 'trBoundedSet' for XXX would yield:
--
-- > BoundedSetOfXXX(n,a,b) ==
-- >   IF n = 0
-- >   THEN     [ cons : {"A"}, arg0 : a ]
-- >   ELSE     [ cons : {"B"}, arg0 : b , arg1 : BoundedSetOfXXX(n-1,a,b) ]
-- >     \union [ cons : {"C"}, arg0 : BoundedSetOfXXX(n-1,a,b) ]
-- >
-- > SetOfXXX(a,b) == UNION { BoundedSetOfXXX(n,a,b) : n \in 0 .. MAXDEPTH }
--
trBoundedSetDef :: (MonadPirouette m) => Name -> [(Name, R.Kind)] -> [(Name, PrtType)] -> TlaT m [TLA.AS_UnitDef]
trBoundedSetDef tyName tyVars cons = do
  let tyArgs    = zipWith (\i (n, _) -> R.tyPure $ R.B (R.Ann n) $ fromIntegral i) (reverse [0 .. length tyVars - 1]) tyVars
  let tlaTyRes  = R.TyApp (R.F $ TyFree tyName) tyArgs
  let tlaTyArgs = map (TlaTyOp []) tyArgs
  let tlaTy     = tlaAll tyVars (TlaTyOp tlaTyArgs tlaTyRes)
  let tlaTyB    = tlaAll tyVars (TlaTyOp (tlaTyNat : tlaTyArgs) tlaTyRes)

  tlaDeclTypeOf (tlaIdentPrefixed "BoundedSetOf" tyName) tlaTyB
  tlaDeclTypeOf (tlaIdentPrefixed "SetOf" tyName)        tlaTy
  (recCons, baseCons) <- splitByM (tlaPure . consIsRecursive tyName . fst) cons
  return $ if null recCons
           then [setOfDecl (bsetOfBody baseCons [])]
           else [bsetOfRecDecl, bsetOfDecl baseCons recCons, setOfDecl setOfBody]
  where
    splitByM f [] = return ([],[])
    splitByM f (x:xs) = dec <$> f x <*> splitByM f xs
      where dec True  = first (x:)
            dec False = second (x:)

    n       = tlaIdent "n"
    nMinus1 = tlaMinus (tlaIdent "n") (tlaNum 1)
    tyVars' = map (tlaIdent . fst) tyVars

    -- SetOfXXX(a,b) == UNION { BoundedSetOfXXX(n,a,b) : n \in 0 .. MAXDEPTH x}
    setOfDecl = TLA.AS_OperatorDef diu False (TLA.AS_OpHead (tlaIdentPrefixed "SetOf" tyName) tyVars')
    setOfBody = tlaUnion $ TLA.AS_SetGeneration di
                  (tlaOpApp (tlaIdentPrefixed "BoundedSetOf" tyName) (n : tyVars'))
                  (TLA.AS_QBoundN [tlaIdent "n"] $ tlaInfix TLA.AS_DOTDOT (tlaNum 1) (tlaIdent "MAXDEPTH"))

    -- RECURSIVE
    bsetOfRecDecl = TLA.AS_RecursiveDecl diu [TLA.AS_OpHead (tlaIdentPrefixed "BoundedSetOf" tyName)
                                                            (map (const $ tlaIdent "_") (n : tyVars'))]

    -- BoundedSetOfXXX(n,b,a) == IF n = 0 THEN baseCases ELSE recursiveCases
    bsetOfDecl b r  = TLA.AS_OperatorDef diu False (TLA.AS_OpHead (tlaIdentPrefixed "BoundedSetOf" tyName) (n : tyVars')) (bsetOfBody b r)
    bsetOfBody b [] = tlaUnions $ map bsetOfCase b
    bsetOfBody b r  = tlaIf (tlaEq n (tlaNum 1)) (tlaUnions $ map bsetOfCase b) (tlaUnions $ map bsetOfCase r)

    bsetOfCase :: (TyName, PrtType) -> TLA.AS_Expression
    bsetOfCase (conName, conTy) =
      let args = fst $ R.tyFunArgs conTy
       in tlaRecordType $ ("cons", tlaSingleton (tlaString conName))
                        -- : ("type", tlaSingleton (tlaString v))
                        : L.zipWith (\ty i -> (argField i, trSimpleType (reverse $ map fst tyVars) ty)) args [0..]

    trSimpleType :: [Name] -> PrtType -> TLA.AS_Expression
    trSimpleType env (R.TyFun t u) = TLA.AS_FunctionType di (trSimpleType env t) (trSimpleType env u)
    trSimpleType env (R.TyApp (R.F (TyFree tn)) args)
      | tn == tyName = tlaOpApp (tlaIdentPrefixed "BoundedSetOf" tn) . (nMinus1:) $ map (trSimpleType env) args
      | otherwise    = tlaOpApp (tlaIdentPrefixed "SetOf" tn) $ map (trSimpleType env) args
    trSimpleType env (R.TyApp (R.F (TyBuiltin n)) args) = tlaOpApp (trBuiltinType n) (map (trSimpleType env) args)
    trSimpleType env (R.TyApp (R.B _ i) args) = tlaOpApp (tlaIdent $ env L.!! fromInteger i) $ map (trSimpleType env) args

trType :: (MonadPirouette m) => PrtType -> TlaT m TLA.AS_Expression
trType (R.TyApp n args)  = tlaOpApp <$> trTypeVar n <*> mapM trType args
trType (R.TyFun t u)     = TLA.AS_FunctionType di <$> trType t <*> trType u
trType (R.TyAll _ _ _)   = throwError' $ PEOther "NotYetImplemented TyAll"
trType (R.TyLam _ _ _)   = throwError' $ PEOther "NotYetImplemented TyLam"

trTypeVar :: (MonadPirouette m) => R.Var Name (TypeBase Name) -> TlaT m TLA.AS_Expression
trTypeVar (R.B (R.Ann n) i) = do
  logWarn "NotYetImplemented Bound type-variable"
  return $ tlaIdentPrefixed "tv" n
trTypeVar (R.F (TyFree n)) = return $ tlaIdentPrefixed "SetOf" n
trTypeVar (R.F (TyBuiltin ty)) = return $ trBuiltinType ty

-- |Translates a constructor and declares it as a TLA operator. For example, calling
--
-- > trConstrDecl [("a", *), ("b", *)] Left (a -> Either a b)
--
-- Will declare "Left" as a constructor with type (with DeBruijn indices):
--
-- > TlaAll "a" * (TlaAll "b" * (TlaOp [TlaVal 1] (Either 1 0)))
--
-- And return a definition for "Left":
--
-- > Left(x) == [cons |-> "Left", arg0 |-> x]
--
trConstrDecl :: (MonadPirouette m) => [(Name, R.Kind)] -> Name -> PrtType -> TlaT m TLA.AS_UnitDef
trConstrDecl tyVars conName conType = do
  let conArity = R.tyArity conType
  let opArgs   = take conArity $ map (TLA.AS_Ident di [] . ('x':) . show) [0..]
  let opHead   = TLA.AS_OpHead (tlaIdent conName) opArgs
  tlaDeclTypeOf (tlaIdent conName) (tlaAll tyVars $ toTlaHdOpType conType)
  return
    $ TLA.AS_OperatorDef diu False opHead
    $ TLA.AS_RecordFunction di
      $ TLA.AS_MapTo (TLA.AS_Field "cons") (TLA.AS_StringLiteral di $ toString conName)
      : L.zipWith (\t i -> TLA.AS_MapTo (TLA.AS_Field ("arg" ++ show i)) t) opArgs [0..]

-- |Similar to 'trConstrDecl' but a little more involved since destructors
-- have a more complex type. Say we're calling 'trDestrDecl' for the Either type:
--
-- > trConstrDecl [("a", *), ("b", *)] Either_match [(Left, a -> Either a b), (Right, b -> Either a b)] Either
--
-- This will register Either_match with type:
--
-- > TlaAll "res" * $ TlaAll "a" * $ TlaAll "b" * $
-- >    $ TlaOp [TlaVal (Either 1 0), TlaOp [1] 2 , TlaOp [0] 2] 2
--
-- The definition for Either_match is a case statement on the cons field on the first argument.
trDestrDecl :: (MonadPirouette m) => [(Name, R.Kind)] -> Name -> [(Name, PrtType)] -> Name -> TlaT m TLA.AS_UnitDef
trDestrDecl tyVars destrName tyCons tyName = do
  -- Start by constructing the TlaType of the destructor:
  let tyRes  = R.tyPure (R.B (fromString "res") (fromIntegral $ length tyVars))
  let tyArgs = TlaVal (tyApp tyName tyVars)
             : map (flip tlaOp tyRes . map TlaVal . fst . R.tyFunArgs . snd) tyCons
  let ty     = TlaAll (fromString "res") R.KStar $ tlaAll tyVars $ tlaOp tyArgs tyRes
  tlaDeclTypeOf (tlaIdent destrName) ty
  -- Now move on the building the term
  let x      = tlaIdent "x"
  let consAr = map (second R.tyArity) tyCons
  let opArgs = x : map (uncurry toOpArg) consAr
  let opHead = TLA.AS_OpHead (tlaIdent destrName) opArgs
  return
    $ TLA.AS_OperatorDef diu False opHead
    $ caseof
    $ map (uncurry toCaseArm) consAr
  where
    toOpArg n 0 = tlaIdentPrefixed "c" n
    toOpArg n i = TLA.AS_OpApp di (tlaIdentPrefixed "c" n) (replicate i (TLA.AS_Ident di [] "_"))

    caseof [] = tlaBool False
    caseof [TLA.AS_CaseArm _ _ e] = e
    caseof arms = TLA.AS_Case di arms Nothing

    toCaseArm cons ar = TLA.AS_CaseArm di (matches (tlaIdent "x") cons) (apply cons ar)

    apply cons ar = TLA.AS_OpApp di (tlaIdentPrefixed "c" cons)
                  $ map (\i -> TLA.AS_InfixOP di TLA.AS_DOT (tlaIdent "x") (tlaIdentPrefixed "arg" $ show i))
                        [0..ar-1]

    matches x cons = TLA.AS_InfixOP di TLA.AS_EQ
                       (tlaProj x onCons)
                       (TLA.AS_StringLiteral di (toString cons))

trBuiltinType :: PIRType -> TLA.AS_Expression
trBuiltinType PIRTypeInteger    = tlaIdentPrefixed "Plutus" "Integer"
trBuiltinType PIRTypeByteString = tlaIdentPrefixed "Plutus" "ByteString"
trBuiltinType PIRTypeChar       = tlaIdentPrefixed "Plutus" "Char"
trBuiltinType PIRTypeUnit       = tlaIdentPrefixed "Plutus" "Unit"
trBuiltinType PIRTypeBool       = tlaIdentPrefixed "Plutus" "Bool"
trBuiltinType PIRTypeString     = tlaIdentPrefixed "Plutus" "String"
trBuiltinType (PIRTypeList t) =
  TLA.AS_OpApp di (tlaIdentPrefixed "Plutus" "List") [trBuiltinType t]
trBuiltinType (PIRTypePair t u) =
  TLA.AS_OpApp di (tlaIdentPrefixed "Plutus" "Pair") [trBuiltinType t, trBuiltinType u]

-- |Returns a TLA quantifier bound. It is used in, for example,
--
-- > \E x \in $(trType tyX) : SomeAct(x)
--      ^^^^^^^^^^^^^^^^^^^
--
trQBoundN :: (MonadPirouette m) => Name -> PrtType -> TlaT m TLA.AS_QBoundN
trQBoundN n ty = TLA.AS_QBoundN [tlaIdent n] <$> trType ty

-- *** Translating Terms

-- |The main term to be translated to TLA gets symbolically 'execute'd into
-- a 'CTree'. The 'trTree' function will translate the given 'CTree' into an /Action Formula/,
-- that is, a formula that relates the prestate to the posttate.
-- To do so, it relies on the 'TLAExprWrapper' which instructs us on how
-- to make the result of 'trTree' into an action formula. A good example
-- of a wrapper is:
--
-- > mkTLAWrapper "LET res == ___ IN globalState' = res.arg0 /\ TxConstraints' = res.arg1"
--
-- For that particular wrapper, the end result of @trTree (Result x)@ would be:
--
-- > WrappedDec == \E m \in TypeM : LET res == x
-- >                                 IN globalState' = res.arg0
-- >                                 /\ TxConstraints' = res.arg1
--
trTree :: (MonadPirouette m) => CTree Name -> PrtType -> TlaT m TLA.AS_Expression
trTree (Result t)             ty =
  asks (wrapExp . toActionWrapper) <*> trTerm t (TlaVal ty)
trTree (Choose x pirTy cases) tyRes = do
  spz <- asks ((=<<) . toSpecialize) <*> return (nameOf pirTy)
  case spz of
    Just tySpz ->
      tlaOr <$> mapM (uncurry $ trSpecializedConstrainedExp tySpz x pirTy tyRes) cases
    Nothing -> do
      (nx, ctx) <-
        case x of
          R.App (R.B (R.Ann n) _) [] -> return (tlaIdent n, id)
          _ -> do
            nx <- tlaFreshName
            tx <- trTerm x (TlaVal pirTy)
            return (nx, tlaLet [tlaAssign nx tx])
      ctx . tlaOr <$>
        mapM (\(cstr,tr) -> trConstrainedExp nx pirTy cstr (trTree tr tyRes)) cases
  where
    nameOf :: PrtType -> Maybe String
    nameOf (R.TyApp (R.B (R.Ann x) _) []) =
      Just $ T.unpack (nameString x)
    nameOf (R.TyApp (R.F (TyFree x)) []) =
      Just $ T.unpack (nameString x)
    nameOf _ = Nothing

trSpecializedConstrainedExp :: (MonadPirouette m)
                            => TypeSpecializer -> PrtTerm -> PrtType -> PrtType
                            -> Constraint Name -> CTree Name
                            -> TlaT m TLA.AS_Expression
trSpecializedConstrainedExp tySpz x pirTy tyRes (Match c args) tr = do
  x' <- trTerm x (TlaVal pirTy)
  fresh <- tlaFreshName
  spzMatch tySpz x' c (map fst args) fresh <$> trTree tr tyRes

-- |Constructs a tla expression constrained by a 'Constraint'. This will take care of our "pattern-matching",
-- translating equivalences and registering facts alongside the main execution path.
trConstrainedExp :: (MonadPirouette m)
                 => TLA.AS_Expression -> PrtType -> Constraint Name -> TlaT m TLA.AS_Expression
                 -> TlaT m TLA.AS_Expression
trConstrainedExp nx ty (Match c args) mexp = do
  exp <- tlaWithDeclTypeOf ((nx, TlaVal ty) : map (tlaIdent *** TlaVal) args) mexp
  return $ tlaAnd
    [ tlaEq (tlaProj nx onCons) (tlaString c)
    , (\l -> if null l then exp else tlaLet l exp) $
        L.zipWith
          (\(n, ty) i -> tlaAssign (tlaIdent n) (tlaProj nx (onArg i)))
          args [0..]
    ]

-- |When translating the body of a PrtTerm, we also receive the 'TlaType' that we expect
-- from the translation. For example, the Just constructor is declared with
-- the following TLA type:
--
-- > TlaAll a * (TlaOp [TlaVal a] (TlaVal (Maybe a)))
--
-- Hence, say we're translating a term @Just (\x -> x + 1)@ in a place that
-- expects a value of type @Maybe Integer@:
--
-- > $[| trTerm "Just (\x -> x + 1)" (TlaVal (Maybe Integer)) |]
-- >   == Just( $[| trTerm "\x -> x + 1" (TlaVal (Integer -> Integer)) |] )
-- >   == Just( [x \in PlutusInteger |-> x + 1] )
--
-- On the first step, we get the type of @Just@ and observe it is an
-- operator whose first (and only) argument must be a value. Hence,
-- @Just@ is applied as an operator, but the first argument is becomes
-- a TLA+ function
--
-- IF we were translating the destructor for @Maybe@, this would have been
-- different:
--
-- > trTerm "Maybe_match m 0 (\x -> x + 1)"
-- >   == Maybe_match(m, 0, LAMBDA x : x + 1)
--
-- That's because @Maybe_match@ has TlaType:
--
-- > TlaAll res * $ TlaAll a * $ TlaOp [TlaVal (Maybe a), TlaVal res, TlaOp [a] res] res
--
-- Hence, when translating the @(\x -> x + 1)@ in this context, we know re're translating
-- it as a 'TlaOp'
--
trTerm :: forall m . (MonadPirouette m) => PrtTerm -> TlaType -> TlaT m TLA.AS_Expression
trTerm = go
  where
    lamOrFun (TlaVal _)   x ty body = tlaFun x ty body
    lamOrFun (TlaOp _  _) x ty body = tlaLambda x ty body

    tlaLambda x _ (TLA.AS_Lambda _ ys t) = TLA.AS_Lambda di (x:ys) t
    tlaLambda x _ t                      = TLA.AS_Lambda di [x] t

    tlaFun x ty (TLA.AS_QuantifierBoundFunction _ l t) =
      TLA.AS_QuantifierBoundFunction di (TLA.AS_QBoundN [x] ty : l) t
    tlaFun x ty t =
      TLA.AS_QuantifierBoundFunction di [TLA.AS_QBoundN [x] ty] t

    go R.Abs {} _ = throwError' $ PEOther "NotYetImplemented trTerm Type Abstractions"
    go (R.Lam (R.Ann x) tyx t) ty =
      lamOrFun ty (tlaIdent x) <$> trType tyx
                               <*> tlaWithDeclTypeOf [(tlaIdent x, TlaVal tyx)] (go t $ tlaTyRet ty)
    go (R.App x [])   ctxTy = do
      xTy         <- tlaTypeOf x
      case (tlaTyDropAll ctxTy, tlaTyDropAll xTy) of
        (TlaOp exp _, TlaOp arX _) ->
          let expAr = length exp in
          case compare expAr (length arX) of
            -- If the context wants an arity and x has this arity,
                     -- there is nothing to be done.
            EQ -> trTermVar x []
            -- When the expectation of the context is of a higher arity
            -- than x, we need eta-expanse the operator.
            GT -> do
              ns <- replicateM expAr tlaFreshName
              TLA.AS_Lambda di ns <$> trTermVar x ns
            -- When the expectation of the context is of a lower arity
            -- than x, we need to coerce operator into function.
            LT -> do
              ns <- replicateM (length arX) tlaFreshName
              let (lamVars, funVars) = splitAt expAr ns
              TLA.AS_Lambda di lamVars <$>
                (mkFun funVars (drop expAr arX) =<< trTermVar x ns)
        (TlaVal _   , TlaOp arX _) -> do
          -- We assume that `arX` is not empty,
          -- otherwise, it should be a `TlaVal`
          ns <- replicateM (length arX) tlaFreshName
          mkFun ns arX =<< trTermVar x ns
        (TlaOp exp _, TlaVal _)    -> do
          -- Same here, `exp` is not empty.
          ns <- replicateM (length exp) tlaFreshName
          TLA.AS_Lambda di ns <$> trTermVar x ns
        (TlaVal _   , TlaVal _)    -> trTermVar x []

        _ -> throwError' $ PEOther $
              "Ctx wants: " ++ renderSingleLineStr (pretty ctxTy)
                                              ++  "; x is: " ++ renderSingleLineStr (pretty xTy)

    go t@(R.App x args) ctxTy = do
      let termArgs = mapMaybe R.fromArg args
      xTy         <- tlaTypeOf x
      let arityX = length (tlaTyArgs $ tlaTyDropAll xTy)
      args' <- zipWithM go termArgs (tlaTyArgs $ tlaTyDropAll xTy)
      case (tlaTyDropAll ctxTy, tlaTyDropAll xTy) of
        (TlaOp exp _, TlaOp arX _) ->
          let expAr = length exp in
          -- If the number of arguments is bigger than the arity of x,
          -- it is the easy case.
          if length termArgs >= arityX
          then do
            excessArgs <-
              mapM
                (\x -> go x (TlaVal undefined))
                (drop arityX termArgs)
            -- One just has to add lambdas to match the expected outer arity
            ns <- replicateM expAr tlaFreshName
            TLA.AS_Lambda di ns <$>
              trTermVar x (args' ++ excessArgs ++ ns)
          -- If arguments are missing, one as to eta expanse, with lambdas,
          -- TLA function or both depending of the expected outer arity.
          else
            let missing = arityX - length termArgs in
            if expAr >= missing
            then do
              ns <- replicateM expAr tlaFreshName
              TLA.AS_Lambda di ns <$> trTermVar x (args' ++ ns)
            else do
              ns <- replicateM missing tlaFreshName
              let (lamVars, funVars) = splitAt expAr (args' ++ ns)
              TLA.AS_Lambda di lamVars <$>
                (mkFun funVars (drop expAr arX) =<< trTermVar x (args' ++ ns))
        (TlaVal _   , TlaOp arX _) ->
          if length termArgs >= arityX
          then do
            excessArgs <-
              mapM
                (\x -> go x (TlaVal undefined))
                (drop arityX termArgs)
            trTermVar x (args' ++ excessArgs)
          -- If arguments are missing, one as to eta expanse, with lambdas,
          -- TLA function or both depending of the expected outer arity.
          else
            let missing = arityX - length termArgs in
            if missing == 0
            then do
              trTermVar x args'
            else do
              ns <- replicateM missing tlaFreshName
              mkFun (args' ++ ns) arX =<< trTermVar x (args' ++ ns)
        (TlaOp exp _, TlaVal _)    -> do
          let expAr = length exp
          excessArgs <-
            mapM (\x -> go x (TlaVal undefined)) termArgs
          ns <- replicateM expAr tlaFreshName
          TLA.AS_Lambda di ns <$>
            trTermVar x (args' ++ excessArgs ++ ns)
        (TlaVal _   , TlaVal _)    -> do
          excessArgs <-
            mapM (\x -> go x (TlaVal undefined)) termArgs
          trTermVar x (args' ++ excessArgs)
        _ -> throwError' $ PEOther $
              "Ctx wants: " ++ renderSingleLineStr (pretty ctxTy)
                ++  "; x is: " ++ renderSingleLineStr (pretty xTy)

mkFun :: (MonadPirouette m)
      => [TLA.AS_Expression] -> [TlaType] -> TLA.AS_Expression
      -> TlaT m TLA.AS_Expression
mkFun []   _   res = return res
mkFun vars tys res =
  flip (TLA.AS_QuantifierBoundFunction di) res <$>
    zipWithM mkQBoundN vars tys
  where
    mkQBoundN v ty = TLA.AS_QBoundN [v] <$> trTlaType ty

    trTlaType (TlaVal b) = trType b

{-
functionalize :: (MonadPirouette m)
              => Int -> TlaType
              -> TlaT m ([TLA.AS_Expression], TLA.AS_Expression -> TLA.AS_Expression)
functionalize n t@(TlaOp args _)
  | n == length args = return ([], id)
  | otherwise = tlaPushCtx "functionalize" $ do
    ns  <- mapM (const tlaFreshNameStr) (drop n args)
    tys <- zipWithM (\n
            -> \case
                 (TlaVal t) -> trQBoundN (fromString n) t
                 _          -> do
                   tlaPure $ logWarn $ renderSingleLineStr (pretty t)
                   throwError' $ PEOther "I don't know how to functionalize this yet"
            ) ns (drop n args)
    if null tys
    then return ([], id)
    else return (map tlaIdent ns , TLA.AS_QuantifierBoundFunction di tys)
functionalize n t = tlaPushCtx "functionalize" $ do
  tlaPure $ logTrace $ "Polymorphic type: " ++ renderSingleLineStr (pretty t)
  case tlaTyDropAll t of
    TlaOp opArgs _ ->
      if length opArgs == n
      then return ([], id)
      else throwError' $ PEOther "trying to functionalize partially applied polymorphic type"
    _ -> throwError' $ PEOther "trying to functionalize non-operator type"
-}

tlaTypeOf :: (MonadPirouette m) => R.Var Name (PIRBase P.DefaultFun Name) -> TlaT m TlaType
tlaTypeOf (R.F f)           = tlaTypeOfFreeName f
tlaTypeOf (R.B (R.Ann n) _) = tlaTypeOfName n

tlaTypeOfName :: (MonadPirouette m) => Name -> TlaT m TlaType
tlaTypeOfName n = tlaPushCtx ("tlaTypeOfName " ++ show n) $ do
  mty <- gets (M.lookup (tlaIdent n) . tsTypeOf)
  case mty of
    Just ty -> return ty
    Nothing -> return $ TlaVal (error $ "Using type of undeclared name: " ++ show n)

tlaTypeOfFreeName :: (MonadPirouette m) => PIRBase P.DefaultFun Name -> TlaT m TlaType
tlaTypeOfFreeName (FreeName n) = tlaTypeOfName n
tlaTypeOfFreeName (Builtin b)  = return $ tlaTyBuiltin b
tlaTypeOfFreeName (Constant c) = return $ tlaTyConstant c
tlaTypeOfFreeName Bottom       = return tlaTyBool

-- TODO: We registered substitutions when producing the actions,
-- where to we need to apply them? I think it is here, on the bound variable
-- case.
trTermVar :: (MonadPirouette m)
          => R.Var Name (PIRBase P.DefaultFun Name)
          -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
trTermVar (R.B (R.Ann n) _)  args = tlaAppName n args
trTermVar (R.F Bottom)       []   = return $ TLA.AS_Bool di False
trTermVar (R.F (Constant c)) []   = trTermConstant c
trTermVar (R.F (Builtin b))  args = trBuiltin b args
trTermVar (R.F (FreeName n)) args = trFreeName n args
trTermVar (R.F t) args            = throwError' $ PEOther "InvalidTermVar"

trFreeName :: (MonadPirouette m) => Name -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
trFreeName n args = do
  nDef <- tlaPure (defOf n)
  case nDef of
    DConstructor _ ty -> trConstrApp n args
    DDestructor ty    -> trDestrApp n ty args
    DFunction r df ty -> do
      tlaAppName n args
    DTypeDef _        -> throwError' $ PEOther "trFreeName: Found TypeDef where a term was expected"

-- |Constructs a value of a datatype as a TLA expression.
trConstrApp :: (MonadPirouette m) => Name -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
trConstrApp = tlaAppName

-- |Constructs a value of a datatype as a TLA expression.
trDestrApp :: (MonadPirouette m) => Name -> TyName -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
trDestrApp n _ = tlaAppName n

trTermConstant :: (MonadPirouette m) => PIRConstant -> TlaT m TLA.AS_Expression
trTermConstant (PIRConstInteger i) = return $ TLA.AS_Num di i
trTermConstant (PIRConstBool b)    = return $ TLA.AS_Bool di b
trTermConstant (PIRConstString s)  = return $ TLA.AS_StringLiteral di s
trTermConstant c = throwError' $ PEOther $ "NotYetImplemented trTermConstant " ++ show c

-- |Application of a defined name as a TLA expression. This is tricky because
-- the TLA Operator definition corresponding to n will expect the same number of
-- term arguments as n. Any further arguments have to be passed as a TLA function application.
tlaAppName :: (MonadPirouette m) => Name -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
tlaAppName = tlaAppNamePref ""

-- |It might be the case that we want and application of term named @n@, but we want
-- the resulting tla application to refer to `hd` instead.
tlaAppNamePref :: (MonadPirouette m) => String -> Name -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
tlaAppNamePref pref n args = do
  mty   <- gets (M.lookup (tlaIdentPrefixed pref n) . tsTypeOf)
  arity <- case mty of
             Just ty -> return (arity $ tlaTyDropAll ty)
             Nothing -> tlaPure (logWarn $ "Undeclared type for " ++ pref ++ show (toString n)) >> return 0
  let (tas, das) = L.splitAt arity args
  return $ tlaFunApp (tlaOpApp (tlaIdentPrefixed pref n) tas) das

trBuiltin :: (MonadPirouette m) => P.DefaultFun -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
trBuiltin P.AddInteger args           = tlaPartialApp2 (tlaInfix TLA.AS_Plus) args
trBuiltin P.SubtractInteger args      = tlaPartialApp2 (tlaInfix TLA.AS_Minus) args
trBuiltin P.MultiplyInteger args      = tlaPartialApp2 (tlaInfix TLA.AS_Mult) args
trBuiltin P.DivideInteger args        = tlaPartialApp2 (tlaInfix TLA.AS_DIV) args
trBuiltin P.QuotientInteger args      = tlaPartialApp2 (tlaInfix TLA.AS_DIV) args
trBuiltin P.RemainderInteger args     = tlaPartialApp2 (tlaInfix TLA.AS_MOD) args
trBuiltin P.ModInteger args           = tlaPartialApp2 (tlaInfix TLA.AS_MOD) args
trBuiltin P.LessThanInteger args      = tlaPartialApp2 (tlaInfix TLA.AS_LT) args
trBuiltin P.LessThanEqInteger args    = tlaPartialApp2 (tlaInfix TLA.AS_LTEQ) args
trBuiltin P.GreaterThanInteger args   = tlaPartialApp2 (tlaInfix TLA.AS_GT) args
trBuiltin P.GreaterThanEqInteger args = tlaPartialApp2 (tlaInfix TLA.AS_GTEQ) args
trBuiltin P.EqInteger args            = tlaPartialApp2 tlaEq args
trBuiltin P.Concatenate args          = tlaPartialApp2 (tlaInfix TLA.AS_Circ) args
trBuiltin P.Append args               = tlaPartialApp2 (tlaInfix TLA.AS_Circ) args
trBuiltin P.TakeByteString args       = tlaPartialApp2 (tlaApp2 ("Plutus", "TakeByteString")) args
trBuiltin P.DropByteString args       = tlaPartialApp2 (tlaApp2 ("Plutus", "DropByteString")) args
trBuiltin P.EqByteString  args        = tlaPartialApp2 tlaEq args
trBuiltin P.IfThenElse  [x,y,z]       = return $ TLA.AS_IF di x y z
trBuiltin P.SHA2 args                 = tlaPartialApp  (tlaApp1 "SHA2") args
trBuiltin bin args = throwError' $ PEOther $ "InvalidBuiltin " ++ show bin

tlaPartialApp
  :: (MonadPirouette m)
  => (TLA.AS_Expression -> TLA.AS_Expression)
  -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
tlaPartialApp f [] = do
  y <- tlaFreshName
  return $ TLA.AS_Lambda di [y] (f y)
tlaPartialApp f [x] = return $ f x
tlaPartialApp f _   = throwError' $ PEOther "tlaPartialApp: Overapplied f"

tlaPartialApp2
  :: (MonadPirouette m)
  => (TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression)
  -> [TLA.AS_Expression] -> TlaT m TLA.AS_Expression
tlaPartialApp2 f [] = do
  x <- tlaFreshName
  y <- tlaFreshName
  return $ TLA.AS_Lambda di [x, y] (f x y)
tlaPartialApp2 f [x] = do
  y <- tlaFreshName
  return $ TLA.AS_Lambda di [y] (f x y)
tlaPartialApp2 f [x,y] = return $ f x y
tlaPartialApp2 _ _     = throwError' $ PEOther "tlaPartialApp2: Overapplied f"

tlaApp1 :: (TLAIdent n) => n -> TLA.AS_Expression -> TLA.AS_Expression
tlaApp1 f x = tlaOpApp (tlaIdent f) [x]

tlaApp2 :: (TLAIdent n) => n -> TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
tlaApp2 f x y = tlaOpApp (tlaIdent f) [x, y]

isTuple2 :: Name -> Bool
isTuple2 n = nameString n == T.pack "Tuple2"
