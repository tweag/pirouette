{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module declares 'PlutusIR' as a supported language, instantiates all the
--  necessary bits for using the facilities from "Pirouette.Term.Syntax" and provides
--  a translation function 'trProgram' to translate a plutusIR program into a 'PrtTerm'
--  and a map of definitions.
module Language.Pirouette.PlutusIR.ToTerm where

import Control.Arrow (first, second, (&&&))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Set as S
import Language.Pirouette.PlutusIR.Builtins
import Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as SystF
import PlutusCore (DefaultUni (..))
import qualified PlutusCore as P
import qualified PlutusCore.Pretty as P
import qualified PlutusIR.Core.Type as PIR
import Debug.Trace

-- * Translating 'PIR.Type's and 'PIR.Term's

-- | Plutus' Internal Representation AST requires a lot of type variables
--  and constraints; we'll just add a constraint synonym to make it easier
--  to write this everywhere.
type PIRConstraint tyname name fun =
  ( Show fun,
    Show name,
    Show tyname,
    Ord name,
    Ord tyname,
    Eq name,
    ToName name,
    ToName tyname
  )

-- | The translation can raise a certain number of errors, enumerated in 'Err', below
data Err loc
  = NotYetImplemented loc String
  | NoTermBindAllowed loc
  deriving (Eq, Show)

-- | Translating to De Bruijn requires us to keep the stack of bound variables, whereas
--  unravelling let-statements requires us to track the dependencies of each known term.
--  The stack of bound variables is kept in the @Reader@ monad and the dependencies
--  on the @State@ monad.
type TrM loc = StateT (St Name) (ReaderT (Env Name) (Except (Err loc)))

-- | Dependencies are a map from a name to a set of names, we use them to
-- float definitions from let-clauses to the global scope: all the dependencies
-- of a term defined in a let-clause have to become a parameter once that
-- term is floated.
type DepsOf name = M.Map name (S.Set (Dep name))

data Dep name
  = TermDep name (Type BuiltinsOfPIR)
  | TypeDep name SystF.Kind
  deriving (Eq, Show, Ord)

unzipDeps :: [Dep name] -> ([(name, SystF.Kind)], [(name, Type BuiltinsOfPIR)])
unzipDeps [] = ([], [])
unzipDeps (TermDep n ty : ds) = second ((n, ty):) $ unzipDeps ds
unzipDeps (TypeDep n ki : ds) = first ((n, ki):) $ unzipDeps ds

-- | In the state we will keep track of the dependencies of each term we explore and
-- a set of type synonyms, that we will expand as soon as we find them.
data St name = St {
    stDepsOf :: DepsOf name,
    stTypeSynonyms :: M.Map name (Type BuiltinsOfPIR)
  }

stEmpty :: St name
stEmpty = St M.empty M.empty

-- | The translation environment consists of the stack of bound term and type variables.
data Env name = Env
  { termStack :: [(name, Type BuiltinsOfPIR)],
    typeStack :: [(name, SystF.Kind)]
  }

envEmpty :: Env name
envEmpty = Env [] []

pushNames :: [(name, Type BuiltinsOfPIR)] -> Env name -> Env name
pushNames ns env = env {termStack = ns ++ termStack env}

pushName :: name -> Type BuiltinsOfPIR -> Env name -> Env name
pushName n ty env = env {termStack = (n, ty) : termStack env}

pushType :: name -> SystF.Kind -> Env name -> Env name
pushType ty ki env = env {typeStack = (ty, ki) : typeStack env}

pushTypes :: [(name, SystF.Kind)] -> Env name -> Env name
pushTypes ty env = env {typeStack = ty ++ typeStack env}

-- | Translates a program into a list of declarations and a body.
trProgram ::
  forall tyname name loc.
  (PIRConstraint tyname name P.DefaultFun) =>
  PIR.Program tyname name DefaultUni P.DefaultFun loc ->
  Except (Err loc) (Term BuiltinsOfPIR, Decls BuiltinsOfPIR)
trProgram (PIR.Program _ t) = runReaderT (evalStateT (runWriterT (fst <$> trTerm Nothing t)) stEmpty) envEmpty

-- | Translates a program into a list of declarations, ignoring the body.
trProgramDecls ::
  forall tyname name loc.
  (PIRConstraint tyname name P.DefaultFun) =>
  PIR.Program tyname name DefaultUni P.DefaultFun loc ->
  Except (Err loc) (Decls BuiltinsOfPIR)
trProgramDecls = fmap snd . trProgram

-- | Translates a list of bindings into declarations. The recursivity is important since it
--  lets us know whether we can expand a particular binding or not in a later phase.
trBindings ::
  forall tyname name loc.
  (PIRConstraint tyname name P.DefaultFun) =>
  [(PIR.Recursivity, PIR.Binding tyname name DefaultUni P.DefaultFun loc)] ->
  TrM loc (Decls BuiltinsOfPIR)
trBindings bs = do
  -- split the term and the data/type binds; we'll handle the data/type bindings first as
  -- those are simple.
  let (termBinds, datatypeBinds) = unzipWith eitherDataTerm' bs
  datatypeDecls <- mapM (trDataOrTypeBinding . snd) datatypeBinds

  -- make a pass over the terms, determining which context variables they depend on.
  -- This has to be done as a fixpoint calculation because dependencies are transitive.
  -- That is, if f depedends on z, but g depends on f, then g also depends on z.
  bindingCtxDeps (map (second fst . snd) termBinds)
  (terms', additionalDecls) <-
    runWriterT $
      mapM (secondM $ splitSndM fst (uncurry2 trTermType)) termBinds
  let termDeclsList = map (\(r, (n, (t, ty))) -> (n, termToDef r t ty)) terms'
  let termDecls = M.fromList termDeclsList
  return $ termDecls <> additionalDecls <> mconcat datatypeDecls

-- | Runs a simple fixpoint calculation returning a new set of dependencies for
--  the terms that are about to be bound. We need that to modify the terms by passing
--  each one of their dependencies as an additional parameter.
--  This function alters the relevant part of the state monad of 'TrM'.
bindingCtxDeps ::
  forall tyname name loc.
  (PIRConstraint tyname name P.DefaultFun) =>
  [(Name, PIR.Term tyname name DefaultUni P.DefaultFun loc)] ->
  TrM loc ()
bindingCtxDeps termBinds = do
  deps <- gets stDepsOf
  deps' <- go termBinds deps M.empty
  modify (\st -> st { stDepsOf = deps' })
  where
    -- The go function below runs a fixpoint computation on a delta over the original dependencies;
    -- We keep computing a new delta until we find nothing different to add;
    go ::
      [(Name, PIR.Term tyname name DefaultUni P.DefaultFun loc)] ->
      DepsOf Name ->
      DepsOf Name ->
      TrM loc (DepsOf Name)
    go xs origDeps delta = do
      vs <- asks termStack
      ts <- asks typeStack
      let currDeps = M.unionWith S.union origDeps delta
      let newDelta = M.fromList $ map (second $ termCtxDeps vs ts currDeps) xs
      if delta == newDelta
        then return currDeps
        else go xs origDeps newDelta

-- | Given a stack of bound variables and a dependency map, compute one step
--  of the transitive dependencies of a term. For example, let @t@ be
--  the term: @\a b -> mult x (add a (g b))@
--
--  Running:
--  > termCtxDeps [w,x,y,z] (M.fromList [(g, {z,w}),(h, {z})]) t
--
--  Will return:
--  > S.fromList {x,z,w}
--
--  That is, the term @t@ depends on {x}, but since it uses @g@
--  and @g@ depends on @z@ and @w@, @t@ depends on all of them.
--
--  The stack of bound variables reflect the variables that were bound by
--  a lambda outside the scope of the current term; hence, in the current term
--  these will be free variables.
termCtxDeps ::
  forall tyname name uni loc.
  (PIRConstraint tyname name P.DefaultFun) =>
  [(Name, Type BuiltinsOfPIR)] ->
  [(Name, SystF.Kind)] ->
  DepsOf Name ->
  PIR.Term tyname name uni P.DefaultFun loc ->
  S.Set (Dep Name)
termCtxDeps vs _ deps (PIR.Var _ n) =
  -- The vs represent the stack of bound variables that were bound OUTSIDE the term we're
  -- looking at. note how we do NOT change vs on the PIR.LamAbs case!
  case L.elemIndex (toName n) (map fst vs) of
    Just i -> S.singleton $ uncurry TermDep $ unsafeIdx "termCtxDeps" vs i
    Nothing -> fromMaybe S.empty $ M.lookup (toName n) deps
termCtxDeps vs ts deps (PIR.LamAbs _ _ _ t) = termCtxDeps vs ts deps t -- TODO: What happens in case there is name shadowing? We'll mess this up!
termCtxDeps vs ts deps (PIR.Apply _ tfun targ) = S.union (termCtxDeps vs ts deps tfun) (termCtxDeps vs ts deps targ)
termCtxDeps vs ts deps (PIR.TyInst _ t i) = tyCtxDeps ts deps i `S.union` termCtxDeps vs ts deps t
termCtxDeps vs ts deps (PIR.TyAbs _ _ _ t) = termCtxDeps vs ts deps t
termCtxDeps vs ts deps (PIR.IWrap _ _ _ t) = termCtxDeps vs ts deps t
termCtxDeps vs ts deps (PIR.Unwrap _ t) = termCtxDeps vs ts deps t
termCtxDeps vs ts deps (PIR.Let _ _ bs t) =
  S.union
    (termCtxDeps vs ts deps t)
    (S.unions (map (either (termCtxDeps vs ts deps . fst . snd) (const S.empty) . eitherDataTerm) $ NE.toList bs))
termCtxDeps _ _ _ _ = S.empty

tyCtxDeps ::
  forall tyname uni loc.
  (ToName tyname) =>
  [(Name, SystF.Kind)] ->
  DepsOf Name ->
  PIR.Type tyname uni loc ->
  S.Set (Dep Name)
tyCtxDeps ts deps (PIR.TyBuiltin _ _) = S.empty
tyCtxDeps ts deps (PIR.TyVar _ n) =
   case L.elemIndex (toName n) (map fst ts) of
    Just i -> S.singleton $ uncurry TypeDep $ unsafeIdx "tyCtxDeps" ts i
    Nothing -> fromMaybe S.empty $ M.lookup (toName n) deps
tyCtxDeps ts deps (PIR.TyFun _ tyA tyB) = tyCtxDeps ts deps tyA `S.union` tyCtxDeps ts deps tyB
tyCtxDeps ts deps (PIR.TyApp _ tyA tyB) = tyCtxDeps ts deps tyA `S.union` tyCtxDeps ts deps tyB
tyCtxDeps ts deps (PIR.TyForall _ _ _ ty) = tyCtxDeps ts deps ty
tyCtxDeps ts deps (PIR.TyLam _ _ _ ty) = tyCtxDeps ts deps ty
tyCtxDeps ts deps (PIR.TyIFix loc ty' ty_tynameuniloc) = undefined

-- | Handles a data/type binding by creating a number of declarations for the constructors
--  and desctructors involved. The type variables declared within a type get duplicated into
--  the 'typeVariables' field of 'Datatype' and into the actual type of constructors.
--  Check the comments for 'Datatype' for an example.
trDataOrTypeBinding ::
  forall tyname name loc.
  (PIRConstraint tyname name P.DefaultFun) =>
  PIR.Binding tyname name DefaultUni P.DefaultFun loc ->
  TrM loc (Decls BuiltinsOfPIR)
trDataOrTypeBinding (PIR.TermBind l _ _ _) = throwError $ NoTermBindAllowed l
trDataOrTypeBinding (PIR.TypeBind _ tyvard tybody) =
  let tyName = toName $ PIR._tyVarDeclName tyvard
   in do
        ty <- trType tybody
        modify (\st -> st { stTypeSynonyms = M.insert tyName ty (stTypeSynonyms st) })
        return M.empty
trDataOrTypeBinding (PIR.DatatypeBind _ (PIR.Datatype _ tyvard args dest cons)) =
  let tyName = toName $ PIR._tyVarDeclName tyvard
      tyKind = trKind $ PIR._tyVarDeclKind tyvard
      tyVars = map ((toName . PIR._tyVarDeclName) &&& (trKind . PIR._tyVarDeclKind)) args
      tyCons = zipWith (\c i -> (toName $ PIR._varDeclName c, DConstructor i tyName)) cons [0 ..]
   in do
        cons' <- mapM (rstr . ((toName . PIR._varDeclName) &&& (trTypeWithArgs tyVars . PIR._varDeclType))) cons
        let tyRes = Datatype tyKind tyVars (toName dest) cons'
        return $
          M.singleton tyName (DTypeDef tyRes)
            <> M.singleton (toName dest) (DDestructor tyName)
            <> M.fromList tyCons

trKind :: PIR.Kind loc -> SystF.Kind
trKind (PIR.Type _) = SystF.KStar
trKind (PIR.KindArrow _ t u) = SystF.KTo (trKind t) (trKind u)

-- | Translates a type with a certain number of arguments pre-declared. These
-- arguments get added as a 'TyAll' to return a well-scoped closed type.
--
-- > trTypeWithArgs [(t1, *), (t2, * -> *)] t
-- >    = TyAll t1 * $ TyAll t2 (* -> *) $ trType t
trTypeWithArgs ::
  (ToName tyname) =>
  [(Name, SystF.Kind)] ->
  PIR.Type tyname DefaultUni loc ->
  TrM loc (Type BuiltinsOfPIR)
trTypeWithArgs env ty = do
  ty' <- local (pushTypes $ reverse env) $ trType ty
  return $ L.foldl' (\t (v, k) -> SystF.TyAll (SystF.Ann v) k t) ty' env

trType ::
  (ToName tyname) =>
  PIR.Type tyname DefaultUni loc ->
  TrM loc (Type BuiltinsOfPIR)
trType (PIR.TyLam _ v k body) =
  SystF.TyLam (SystF.Ann $ toName v) (trKind k) <$> local (pushType (toName v) (trKind k)) (trType body)
trType (PIR.TyForall _ v k body) =
  SystF.TyAll (SystF.Ann $ toName v) (trKind k) <$> local (pushType (toName v) (trKind k)) (trType body)
trType (PIR.TyVar _ tyn) = do
  let tyName = toName tyn
  -- First we try to see if this type is a bound variable
  bounds <- asks (map fst . typeStack)
  case L.elemIndex tyName bounds of
    Just ix -> return $ SystF.TyPure (SystF.Bound (SystF.Ann tyName) $ fromIntegral ix)
    -- If it's not a bound variable, we check whether its a type synonym
    Nothing -> do
      syns <- gets stTypeSynonyms
      case M.lookup (toName tyn) syns of
        Just ty -> return ty
         -- Finally, it's not bound nor a type synonym, we translate it as a "free" name.
        Nothing -> return $ SystF.TyPure (SystF.Free $ TySig tyName)
trType (PIR.TyFun _ t u) = SystF.TyFun <$> trType t <*> trType u
trType (PIR.TyApp _ t u) = SystF.tyApp <$> trType t <*> trType u
trType (PIR.TyBuiltin _ (P.SomeTypeIn uni)) =
  return $ SystF.TyPure (SystF.Free $ TyBuiltin $ defUniToType uni)
trType (PIR.TyIFix l _ _) = throwError $ NotYetImplemented l "TyIFix"

trTermType ::
  forall tyname name loc.
  (PIRConstraint tyname name P.DefaultFun, Ord name) =>
  Name ->
  PIR.Term tyname name DefaultUni P.DefaultFun loc ->
  PIR.Type tyname DefaultUni loc ->
  WriterT
    (Decls BuiltinsOfPIR)
    (TrM loc)
    (Term BuiltinsOfPIR, Type BuiltinsOfPIR)
trTermType n t ty = do
  (t', f) <- trTerm (Just n) t
  (t',) . f <$> lift (trType ty)

-- | Translates a term, which is potentially named, while producing declarations within this
--  term that should be boiled up to the top level. We use the name to compute
--  the dependencies of this term on its context, which become lambda-abstractions.
--  Let @t@ be the term: @\a b -> mult x (add a (g b))@, and assume
--  the current stack of bound variables is @[w,x,y,z]@ and the map of dependencies
--  is @M.fromList [(g, {z,w}),(h, {z})]@, then running @trTerm (Just "t") t@ will return:
--
--  > ([], \w x z -> \a b -> mult x (add a (g z w b)))
--
--  The first component is an empty list of declarations, since @t@ has no let-statements within.
--  The second component is a term that receives all its dependencies as parameters and
--  passes these dependencies around. Note how the call to @g@ also received the necessary deps.
trTerm ::
  forall tyname name loc.
  (PIRConstraint tyname name P.DefaultFun, Ord name) =>
  Maybe Name ->
  PIR.Term tyname name DefaultUni P.DefaultFun loc ->
  WriterT
    (Decls BuiltinsOfPIR)
    (TrM loc)
    (Term BuiltinsOfPIR, Type BuiltinsOfPIR -> Type BuiltinsOfPIR)
trTerm mn t = do
  deps <- gets stDepsOf
  let vs = maybe [] S.toList $ mn >>= (`M.lookup` deps)
  let (tyDeps, termDeps) = unzipDeps vs
  trace ("trTerm " ++ show mn ++ "; tyDeps = " ++ show (map fst tyDeps)) (return ())
  t' <- local (pushNames $ reverse termDeps) (go t)
  let adjustType = flip (foldr (\(_, t0) r -> SystF.TyFun t0 r)) termDeps
  return
    ( foldr (\(n, t0) r -> SystF.Lam (SystF.Ann n) t0 r) t' termDeps,
      adjustType
    )
  where
    go ::
      PIR.Term tyname name DefaultUni P.DefaultFun loc ->
      WriterT (Decls BuiltinsOfPIR) (TrM loc) (Term BuiltinsOfPIR)
    go (PIR.Var _ n) = do
      vs <- asks termStack
      case L.elemIndex (toName n) (map fst vs) of
        Just i -> return $ SystF.termPure (SystF.Bound (SystF.Ann $ toName n) $ fromIntegral i)
        Nothing -> lift . checkIfDep (toName n) $ map fst vs
    go (PIR.Constant _ (P.Some (P.ValueOf tx x))) =
      return $ SystF.termPure $ SystF.Free $ Constant $ defUniToConstant tx x
    go (PIR.Builtin _ f) = return $ SystF.termPure $ SystF.Free $ Builtin f
    go (PIR.Error _ _) = return $ SystF.termPure $ SystF.Free Bottom
    go (PIR.IWrap _ _ _ t0) = go t0 -- VCM: are we sure we don't neet to
    go (PIR.Unwrap _ t0) = go t0 --      preserve the wrap/unwraps?
    go (PIR.TyInst _ t0 ty) = SystF.app <$> go t0 <*> lift (SystF.TyArg <$> trType ty)
    go (PIR.TyAbs _ ty k t0) = do
      SystF.Abs (SystF.Ann $ toName ty) (trKind k) <$> local (pushType (toName ty) (trKind k)) (go t0)
    go (PIR.LamAbs _ n tyd t0) = do
      ty <- lift $ trType tyd
      SystF.Lam (SystF.Ann $ toName n) ty <$> local (pushName (toName n) ty) (go t0)
    go (PIR.Apply _ tfun targ) = SystF.app <$> go tfun <*> (SystF.TermArg <$> go targ)
    -- For let-statements, we will push the (translated) definitions to the top level;
    -- we must be careful and push the variables we've seen so far as a local context
    -- to those definitions.
    go (PIR.Let _ r bs t0) = do
      bs' <- lift (trBindings $ map (r,) $ NE.toList bs)
      tell bs'
      go t0

    -- TODO: Check if dep on types too!
    checkIfDep :: Name -> [Name] -> TrM loc (Term BuiltinsOfPIR)
    checkIfDep n vs = do
      mDepsOn <- gets (M.lookup n . stDepsOf)
      case mDepsOn of
        Nothing -> return $ SystF.termPure $ SystF.Free $ TermSig n
        Just ns -> do
          let args =
                map
                  ( SystF.TermArg . SystF.termPure . uncurry SystF.Bound
                      . (\x -> (SystF.Ann x, fromIntegral $ fromJust $ L.elemIndex x vs))
                      . fst
                  )
                  $ snd $ unzipDeps $ S.toList ns
          return $ SystF.App (SystF.Free $ TermSig n) args

-- A straightforward translation of a PIRTerm to the Pirouette representation of term.
-- This function is not used by `trProgram` which is the main function to translate
-- the file we want to verify.
-- It remains useful however, especially to define transformations using the PIR syntax.
trPIRTerm ::
  PIRConstraint tyname name P.DefaultFun =>
  PIR.Term tyname name DefaultUni P.DefaultFun loc ->
  Except (Err loc) (Term BuiltinsOfPIR)
trPIRTerm t = runReaderT (evalStateT (fst <$> runWriterT (fst <$> trTerm Nothing t)) stEmpty) envEmpty

-- * Some Auxiliary Functions

isRec :: PIR.Recursivity -> Bool
isRec PIR.Rec = True
isRec _ = False

termToDef :: PIR.Recursivity -> Term BuiltinsOfPIR -> Type BuiltinsOfPIR -> Definition BuiltinsOfPIR
termToDef PIR.Rec = DFunction Rec
termToDef PIR.NonRec = DFunction NonRec

eitherDataTerm ::
  (ToName name) =>
  PIR.Binding tyname name uni fun loc ->
  Either
    (Name, (PIR.Term tyname name uni fun loc, PIR.Type tyname uni loc))
    (PIR.Binding tyname name uni fun loc)
eitherDataTerm (PIR.TermBind _ _ vard t) = Left (toName (PIR._varDeclName vard), (t, PIR._varDeclType vard))
eitherDataTerm binding = Right binding

eitherDataTerm' ::
  (ToName name) =>
  (a, PIR.Binding tyname name uni fun loc) ->
  Either
    (a, (Name, (PIR.Term tyname name uni fun loc, PIR.Type tyname uni loc)))
    (a, PIR.Binding tyname name uni fun loc)
eitherDataTerm' (a, x) = either (Left . (a,)) (Right . (a,)) $ eitherDataTerm x

unzipWith :: (c -> Either a b) -> [c] -> ([a], [b])
unzipWith f = foldr (either (first . (:)) (second . (:)) . f) ([], [])

secondM :: (Monad m) => (b -> m b') -> (a, b) -> m (a, b')
secondM f (a, b) = (a,) <$> f b

assocL :: (a, (b, c)) -> ((a, b), c)
assocL (a, (b, c)) = ((a, b), c)

splitSndM :: (Monad m) => (c -> a) -> (c -> m b) -> c -> m (a, b)
splitSndM f g x = (f x,) <$> g x

rstr :: (Monad m) => (a, m b) -> m (a, b)
rstr (a, mb) = (a,) <$> mb

uncurry2 :: (a -> b -> c -> d) -> (a, (b, c)) -> d
uncurry2 f (a, (b, c)) = f a b c

-- * Pretty instances for Plutus-specific goodies

instance ToName P.Name where
  toName pn = Name (P.nameString pn) (Just $ P.unUnique $ P.nameUnique pn)

instance ToName P.TyName where
  toName = toName . P.unTyName

instance Pretty P.DefaultFun where
  pretty = P.pretty
