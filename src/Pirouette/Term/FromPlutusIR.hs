{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE PatternSynonyms      #-}

module Pirouette.Term.FromPlutusIR where

import           Pirouette.Term.Syntax
import qualified Pirouette.Term.Syntax.SystemF as R

import           PlutusCore         ( DefaultUni(..)
                                    , pattern DefaultUniList
                                    , pattern DefaultUniString
                                    , pattern DefaultUniPair )
import qualified PlutusCore         as P
import qualified PlutusCore.Pretty  as P
import qualified PlutusIR.Core.Type as PIR

import qualified Data.ByteString    as BS
import           Data.Data
import           Data.Typeable
import qualified Data.Text          as T
import qualified Data.List          as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map           as M
import qualified Data.Set           as S
import           Data.Maybe         (fromMaybe, fromJust)
import           Data.Text.Prettyprint.Doc

import           Control.Arrow (first, second, (&&&), (***))
import           Control.Monad.Except
import           Control.Monad.Writer
import           Control.Monad.State
import           Control.Monad.Reader

import Debug.Trace

-- |Plutus' Internal Representation AST requires a lot of type variables
-- and constraints; we'll just add a constraint synonym to make it easier
-- to write this everywhere.
type PIRConstraint tyname name fun
  = ( Show fun
    , Show name
    , Show tyname
    , Ord name, Ord tyname
    , Eq name
    , ToName name, ToName tyname
    )

-- |The translation can raise a certain number of errors, enumerated in 'Err', below
data Err loc
  = NotYetImplemented loc String
  | NoTermBindAllowed loc
  | ApplicationError
  deriving (Eq, Show)

-- |Translating to De Bruijn requires us to keep the stack of bound variables, whereas
-- unravelling let-statements requires us to track the dependencies of each known term.
-- The stack of bound variables is kept in the @Reader@ monad and the dependencies
-- on the @State@ monad.
type TrM loc = StateT (DepsOf Name) (ReaderT (Env Name) (Except (Err loc)))

-- |Dependencies are a map from a name to a set of names.
type DepsOf name = M.Map name (S.Set (name, Type name))

-- |The translation environment consists of the stack of bound variables.
data Env name = Env
  { termStack :: [(name, Type name)]
  , typeStack :: [name]
  }

envEmpty :: Env name
envEmpty = Env [] []

pushNames :: [(name, Type name)] -> Env name -> Env name
pushNames ns env = env { termStack = ns ++ termStack env }

pushName :: name -> Type name -> Env name -> Env name
pushName n ty env = env { termStack = (n, ty) : termStack env }

pushType :: name -> Env name -> Env name
pushType ty env = env { typeStack = ty : typeStack env }

pushTypes :: [name] -> Env name -> Env name
pushTypes ty env = env { typeStack = ty ++ typeStack env }

-- |Translates a program into a list of declarations and a body.
trProgram :: forall tyname name fun loc
           . (PIRConstraint tyname name fun)
          => PIR.Program tyname name DefaultUni fun loc
          -> Except (Err loc) (Term Name fun, Decls Name fun)
trProgram (PIR.Program _ t) = runReaderT (evalStateT (runWriterT (fst <$> trTerm Nothing t)) M.empty) envEmpty

-- |Translates a program into a list of declarations, ignoring the body.
trProgramDecls :: forall tyname name fun loc
                . (PIRConstraint tyname name fun)
               => PIR.Program tyname name DefaultUni fun loc
               -> Except (Err loc) (Decls Name fun)
trProgramDecls = fmap snd . trProgram

-- |Translates a list of bindings into declarations. The recursivity is important since it
-- lets us know whether we can expand a particular binding or not in a later phase.
trBindings :: forall tyname name fun loc
               . (PIRConstraint tyname name fun)
              => [(PIR.Recursivity, PIR.Binding tyname name DefaultUni fun loc)]
              -> TrM loc (Decls Name fun)
trBindings bs = do
  -- split the term and the data/type binds; we'll handle the data/type bindings first as
  -- those are simple.
  let (termBinds, datatypeBinds) = unzipWith eitherDataTerm' bs
  datatypeDecls <- mapM (trDataOrTypeBinding . snd) datatypeBinds
  -- make a pass over the terms, determining which context variables they depend on.
  -- This has to be done as a fixpoint calculation because dependencies are transitive.
  -- That is, if f depedends on z, but g depends on f, then g also depends on z.
  deps <- bindingCtxDeps (map (second fst . snd) termBinds)
  (terms', additionalDecls) <- runWriterT
                             $ mapM (secondM $ splitSndM fst (uncurry2 trTermType)) termBinds
  let termDeclsList = map (\(r , (n, (t , ty))) -> (n , termToDef r t ty)) terms'
  let termDecls = M.fromList termDeclsList
  return $ termDecls <> additionalDecls <> mconcat datatypeDecls

-- |Runs a simple fixpoint calculation returning a new set of dependencies for
-- the terms that are about to be bound. We need that to modify the terms by passing
-- each one of their dependencies as an additional parameter.
bindingCtxDeps :: forall tyname name fun loc
                . (PIRConstraint tyname name fun)
               => [(Name, PIR.Term tyname name DefaultUni fun loc)]
               -> TrM loc ()
bindingCtxDeps termBinds = do
  deps  <- get
  deps' <- go termBinds deps M.empty
  put deps'
  where
    -- The go function below runs a fixpoint computation on a delta over the original dependencies;
    -- We keep computing a new delta until we find nothing different to add.
    go :: [(Name, PIR.Term tyname name DefaultUni fun loc)]
       -> DepsOf Name
       -> DepsOf Name
       -> TrM loc (DepsOf Name)
    go xs origDeps delta = do
      vs <- asks termStack
      let currDeps = M.unionWith S.union origDeps delta
      let newDelta = M.fromList $ map (second $ termCtxDeps vs currDeps) xs
      if newDelta == delta
      then return currDeps
      else go xs origDeps newDelta

-- |Given a stack of bound variables and a dependency map, compute one step
-- of the transitive dependencies of a term. For example, let @t@ be
-- the term: @\a b -> mult x (add a (g b))@
--
-- Running:
-- > termCtxDeps [w,x,y,z] (M.fromList [(g, {z,w}),(h, {z})]) t
--
-- Will return:
-- > S.fromList {x,z,w}
--
-- That is, the term @t@ depends on {x}, but since it uses @g@
-- and @g@ depends on @z@ and @w@, @t@ depends on all of them.
--
-- The stack of bound variables reflect the variables that were bound by
-- a lambda outside the scope of the current term; hence, in the current term
-- these will be free variables.
termCtxDeps :: forall tyname name uni fun loc
             . (PIRConstraint tyname name fun)
            => [(Name, Type Name)]
            -> DepsOf Name
            -> PIR.Term tyname name uni fun loc
            -> S.Set (Name, Type Name)
termCtxDeps vs deps (PIR.Var l n) =
  -- The vs represent the stack of bound variables that were bound OUTSIDE the term we're
  -- looking at. note how we do NOT change vs on the PIR.LamAbs case!
  case L.elemIndex (toName n) (map fst vs) of
    Just i  -> S.singleton (unsafeIdx "termCtxDeps" vs i)
    Nothing -> fromMaybe S.empty $ M.lookup (toName n) deps
termCtxDeps vs deps (PIR.LamAbs _ _ _ t)    = termCtxDeps vs deps t -- TODO: What happens in case there is name shadowing? We'll mess this up!
termCtxDeps vs deps (PIR.Apply _ tfun targ) = S.union (termCtxDeps vs deps tfun) (termCtxDeps vs deps targ)
termCtxDeps vs deps (PIR.TyInst _ t _)      = termCtxDeps vs deps t
termCtxDeps vs deps (PIR.TyAbs _ _ _ t)     = termCtxDeps vs deps t
termCtxDeps vs deps (PIR.IWrap _ _ _ t)     = termCtxDeps vs deps t
termCtxDeps vs deps (PIR.Unwrap _ t)        = termCtxDeps vs deps t
termCtxDeps vs deps (PIR.Let _ _ bs t)      =
  S.union (termCtxDeps vs deps t)
          (S.unions (map (either (termCtxDeps vs deps . fst . snd) (const S.empty) . eitherDataTerm) $ NE.toList bs))
termCtxDeps _ _ _ = S.empty

-- |Handles a data/type binding by creating a number of declarations for the constructors
-- and desctructors involved.
trDataOrTypeBinding
  :: forall tyname name fun loc
   . (PIRConstraint tyname name fun)
  => PIR.Binding tyname name DefaultUni fun loc
  -> TrM loc (Decls Name fun)
trDataOrTypeBinding (PIR.TermBind l _ _ _) = throwError $ NoTermBindAllowed l
trDataOrTypeBinding (PIR.TypeBind l _ _) = throwError $ NotYetImplemented l "type-bind"
trDataOrTypeBinding (PIR.DatatypeBind _ (PIR.Datatype _ tyvard args dest cons)) =
  let tyName = toName $ PIR.tyVarDeclName tyvard
      tyKind = trKind $ PIR.tyVarDeclKind tyvard
      tyVars = map ((toName . PIR.tyVarDeclName) &&& (trKind . PIR.tyVarDeclKind)) args
      tyCons = zipWith (\c i -> (toName $ PIR.varDeclName c, DConstructor i tyName)) cons [0..]
   in do
     cons' <- mapM (rstr . ((toName . PIR.varDeclName) &&& (trTypeWithArgs tyVars . PIR.varDeclType))) cons
     let tyRes = Datatype tyKind tyVars (toName dest) cons'
     return $ M.singleton tyName (DTypeDef tyRes)
           <> M.singleton (toName dest) (DDestructor tyName)
           <> M.fromList tyCons
  where
    nbArrows :: PIR.Type tyname uni ann -> Int
    nbArrows (PIR.TyFun _ _ t) = 1 + nbArrows t
    nbArrows t = 0

trKind :: PIR.Kind loc -> R.Kind
trKind (PIR.Type _)          = R.KStar
trKind (PIR.KindArrow _ t u) = R.KTo (trKind t) (trKind u)

trTypeWithArgs :: (ToName tyname)
               => [(Name, R.Kind)] -> PIR.Type tyname DefaultUni loc -> TrM loc (Type Name)
trTypeWithArgs env = local (pushTypes $ reverse $ map fst env) . trType

trType :: (ToName tyname)
       => PIR.Type tyname DefaultUni loc -> TrM loc (Type Name)
trType (PIR.TyLam l v k body)    =
  R.TyLam (R.Ann $ toName v) (trKind k) <$> local (pushType $ toName v) (trType body)
trType (PIR.TyForall l v k body) =
  R.TyAll (R.Ann $ toName v) (trKind k) <$> local (pushType $ toName v) (trType body)
trType (PIR.TyVar _ tyn) =
  asks ( R.tyPure
       . maybe (R.F $ TyFree $ toName tyn) (R.B (R.Ann $ toName tyn) . fromIntegral)
       . L.elemIndex (toName tyn)
       . typeStack)
trType (PIR.TyFun _ t u)      = R.TyFun <$> trType t <*> trType u
trType (PIR.TyApp _ t u)      = R.tyApp <$> trType t <*> trType u
trType (PIR.TyBuiltin _ (P.SomeTypeIn uni))
  = return $ R.tyPure (R.F $ TyBuiltin $ defUniToType uni)
trType (PIR.TyIFix l _ _)     = throwError $ NotYetImplemented l "TyIFix"

trTermType :: forall tyname name fun loc
            . (PIRConstraint tyname name fun, Ord name)
           => Name
           -> PIR.Term tyname name DefaultUni fun loc
           -> PIR.Type tyname DefaultUni loc
           -> WriterT (Decls Name fun)
                      (TrM loc)
                      (Term Name fun, Type Name)
trTermType n t ty = do
  (t', f) <- trTerm (Just n) t
  (t',) . f <$> lift (trType ty)

-- |Translates a term, which is potentially named, while producing declarations within this
-- term that should be boiled up to the top level. We use the name to compute
-- the dependencies of this term on its context, which become lambda-abstractions.
-- Let @t@ be the term: @\a b -> mult x (add a (g b))@, and assume
-- the current stack of bound variables is @[w,x,y,z]@ and the map of dependencies
-- is @M.fromList [(g, {z,w}),(h, {z})]@, then running @trTerm (Just "t") t@ will return:
--
-- > ([], \w x z -> \a b -> mult x (add a (g z w b)))
--
-- The first component is an empty list of declarations, since @t@ has no let-statements within.
-- The second component is a term that receives all its dependencies as parameters and
-- passes these dependencies around. Note how the call to @g@ also received the necessary deps.
trTerm :: forall tyname name fun loc
        . (PIRConstraint tyname name fun, Ord name)
       => Maybe Name
       -> PIR.Term tyname name DefaultUni fun loc
       -> WriterT (Decls Name fun)
                  (TrM loc)
                  (Term Name fun, Type Name -> Type Name)
trTerm mn t = do
  deps <- get
  let vs = maybe [] S.toList $ mn >>= (`M.lookup` deps)
  t' <- local (pushNames $ reverse vs) (go t)
  let adjustType = flip (foldr (\(_, t) r -> R.TyFun t r)) vs
  return ( foldr (\(n, t) r -> R.Lam (R.Ann n) t r) t' vs
         , adjustType
         )
 where
    go :: PIR.Term tyname name DefaultUni fun loc
       -> WriterT (Decls Name fun) (TrM loc) (Term Name fun)
    go (PIR.Var l n) = do
      vs <- asks termStack
      case L.elemIndex (toName n) (map fst vs) of
        Just i  -> return $ R.termPure (R.B (R.Ann $ toName n) $ fromIntegral i)
        Nothing -> lift . checkIfDep (toName n) $ map fst vs
    go (PIR.Constant _ (P.Some (P.ValueOf tx x))) =
        return $ R.termPure $ R.F $ Constant $ defUniToConstant tx x
    go (PIR.Builtin _ f)         = return $ R.termPure $ R.F $ Builtin f
    go (PIR.Error _ _)           = return $ R.termPure $ R.F Bottom
    go (PIR.IWrap _ ty_a ty_b t) = go t -- VCM: are we sure we don't neet to
    go (PIR.Unwrap _ t)          = go t --      preserve the wrap/unwraps?
    go (PIR.TyInst _ t ty)       = R.app <$> go t <*> lift (R.TyArg <$> trType ty)
    go (PIR.TyAbs _ ty k t)      = do
      R.Abs (R.Ann $ toName ty) (trKind k) <$> local (pushType $ toName ty) (go t)
    go (PIR.LamAbs _ n tyd t)    = do
      ty <- lift $ trType tyd
      R.Lam (R.Ann $ toName n) ty <$> local (pushName (toName n) ty) (go t)
    go (PIR.Apply _ tfun targ)   = R.app <$> go tfun <*> (R.Arg <$> go targ)

    -- For let-statements, we will push the (translated) definitions to the top level;
    -- we must be careful and push the variables we've seen so far as a local context
    -- to those definitions.
    go (PIR.Let l r bs t)  = do
      bs' <- lift (trBindings $ map (r,) $ NE.toList bs)
      tell bs'
      go t

    checkIfDep :: Name -> [Name] -> TrM loc (Term Name fun)
    checkIfDep n vs = do
      mDepsOn <- gets (M.lookup n)
      case mDepsOn of
        Nothing -> return $ R.termPure $ R.F $ FreeName n
        Just ns -> do
          let args = map (R.Arg . R.termPure . uncurry R.B
                          . (\x -> (R.Ann x, fromIntegral $ fromJust $ L.elemIndex x vs)) . fst)
                   $ S.toList ns
          return $ R.App (R.F $ FreeName n) args

--------------------------------
-- Auxiliary Functions Follow --
--------------------------------

isRec :: PIR.Recursivity -> Bool
isRec PIR.Rec = True
isRec _       = False

termToDef :: PIR.Recursivity -> Term Name fun -> Type Name -> Definition Name fun
termToDef PIR.Rec    = DFunction Rec
termToDef PIR.NonRec = DFunction NonRec

eitherDataTerm :: (ToName name)
               => PIR.Binding tyname name uni fun loc
               -> Either (Name, (PIR.Term tyname name uni fun loc, PIR.Type tyname uni loc))
                         (PIR.Binding tyname name uni fun loc)
eitherDataTerm (PIR.TermBind _ _ vard t) = Left (toName (PIR.varDeclName vard), (t, PIR.varDeclType vard))
eitherDataTerm binding                   = Right binding

eitherDataTerm' :: (ToName name)
                => (a, PIR.Binding tyname name uni fun loc)
                -> Either (a, (Name, (PIR.Term tyname name uni fun loc, PIR.Type tyname uni loc)))
                          (a, PIR.Binding tyname name uni fun loc)
eitherDataTerm' (a , x) = either (Left . (a,)) (Right . (a,)) $ eitherDataTerm x

unzipWith :: (c -> Either a b) -> [c] -> ([a], [b])
unzipWith f = foldr (either (first . (:)) (second . (:)) . f) ([], [])

secondM :: (Monad m) => (b -> m b') -> (a , b) -> m (a , b')
secondM f (a , b) = (a,) <$> f b

assocL :: (a , (b , c)) -> ((a , b), c)
assocL (a , (b, c)) = ((a , b) , c)

splitSndM :: (Monad m) => (c -> a) -> (c -> m b) -> c -> m (a , b)
splitSndM f g x = (f x ,) <$> g x

rstr :: (Monad m) => (a , m b) -> m (a , b)
rstr (a , mb) = (a,) <$> mb

uncurry2 :: (a -> b -> c -> d) -> (a, (b, c)) -> d
uncurry2 f (a , (b , c)) = f a b c
