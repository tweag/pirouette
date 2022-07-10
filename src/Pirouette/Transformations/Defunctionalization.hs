{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Transformations.Defunctionalization (defunctionalize) where

import Control.Arrow (first, (***))
import Control.Monad.RWS.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Generics.Uniplate.Data
import Data.List (nub, sortOn)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.String.Interpolate.IsString
import qualified Data.Text as T
import Data.Traversable
import Pirouette.Monad
import Pirouette.Monad.Maybe
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base as B
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.EtaExpand
import Pirouette.Transformations.Utils

defunctionalize :: (Language lang, LanguageBuiltinTypes lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
defunctionalize defs0 = undefined

-- Defunctionalization assumes lots of things! Namelly:
--
-- 1. No polymorphic higher-order function occurence
-- 2. everything has been fully eta-expanded
-- 3. ??? still discovering

{-
defunctionalize :: (Language lang, LanguageBuiltinTypes lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
defunctionalize defs0 =
  case defunctionalizeAssumptions defs0 of
    () -> defs' {prtUODecls = prtUODecls defs' <> typeDecls <> applyFunDecls}
  where
    (defs1, toDefun1) = defunTypes (etaExpandAll defs0)
    defs2 = defunDtors defs1
    (defs3, toDefun2) = defunFuns defs2
    toDefun = toDefun1 `M.union` toDefun2

    (defs', closureCtorInfos) = evalRWS (defunCalls toDefun defs3) mempty (DefunState mempty)

    closureCtorInfos' = sortOn (\c -> (ctorName c, ctorIdx c)) closureCtorInfos

    typeDecls = mkClosureTypes closureCtorInfos'
    applyFunDecls = mkApplyFuns closureCtorInfos'

defunctionalizeAssumptions :: (Language lang) => PrtUnorderedDefs lang -> ()
defunctionalizeAssumptions defs = either error (const ()) . traverseDefs (\n d -> defOk n d >> return d) $ defs
  where
    dtorsNames = S.fromList $ mapMaybe getDtorName (M.elems $ prtUODecls defs)
    getDtorName (DTypeDef Datatype {..}) = Just destructor
    getDtorName _ = Nothing

    hofs = hofsClosure (prtUODecls defs) (findPolyHOFDefs $ prtUODecls defs)

    defOk :: forall lang. (Language lang) => Name -> Definition lang -> Either String ()
    defOk n (DFunDef FunDef {..}) =
      let termAbs = [t | t@SystF.Abs {} <- universe funBody]

          tyArgs :: [Arg lang]
          tyArgs =
            [ thisTyArgs | (SystF.App (SystF.Free (TermSig t)) args) <- universe funBody, t `S.notMember` dtorsNames, thisTyArgs <- filter SystF.isTyArg args, not $ null thisTyArgs
            ]

          tyVars :: [Var lang]
          tyVars = [t | t@(SystF.Bound _ _) <- universeBi funTy]
       in if (TermNamespace, n) `M.member` hofs
            then
              if null termAbs && null tyArgs && null tyVars
                then Right ()
                else
                  Left $
                    "Defunctionalization will fail for: " ++ show n ++ "\n"
                      ++ show termAbs
                      ++ show tyArgs
                      ++ show tyVars
            else Right ()
    defOk _ _ = return ()

-- * Defunctionalization of types

-- | Identify types that contain contructors that receive functions as
-- an argument. As an example, take:
--
-- > data Monoid (a : Type) = Mon : (a -> a -> a) -> a -> Monoid a
-- > data Maybe (a : Type) = Just : a -> Maybe a | Nothing : Maybe a
--
-- The call to 'defunTypes' will pick @Mon@ as a target for defunctionalization,
-- and will 'tell' an appropriate new declaration for @Monoid@. It will
-- not pick @Just@, however.
--
-- TODO: This has to be more involved; we need to generate the proper calls
-- for nested things at once, in this step, for the rest of the engine
-- to understand... my previous hacks met their deadend
defunTypes ::
  (LanguagePretty lang, LanguageBuiltins lang) =>
  PrtUnorderedDefs lang ->
  (PrtUnorderedDefs lang, M.Map Name (HofsList lang))
defunTypes defs = runWriter $ traverseDefs defunTypeDef defs
  where
    defunTypeDef _ (DTypeDef Datatype {..}) = do
      forM_ allMaybeHofs $ \case
        (ctorName, Just hof) -> tell $ M.singleton ctorName hof
        _ -> pure ()
      pure $ DTypeDef Datatype {constructors = ctors', ..}
      where
        (ctors', allMaybeHofs) =
          unzip
            [ ((ctorName, ctorTy'), (ctorName, maybeHofs))
              | (ctorName, ctorTy) <- constructors,
                let (ctorTy', hofs) = rewriteHofType ctorTy
                    maybeHofs
                      | ctorTy' == ctorTy = Nothing
                      | otherwise = Just hofs
            ]
    defunTypeDef _ x = pure x

-- Destructors have a well-known structure: they are η-expanded,
-- they accept a bunch of funargs that needn't be defunctionalized, etc,
-- so we can have a few shortcuts
defunDtors ::
  forall lang.
  (LanguagePretty lang, LanguageBuiltins lang) =>
  PrtUnorderedDefs lang ->
  PrtUnorderedDefs lang
defunDtors defs = transformBi f defs
  where
    f :: Term lang -> Term lang
    f term
      | Just UnDestMeta {..} <- runReader (runMaybeT (unDest term)) defs,
        Datatype {..} <- runReader (prtTypeDefOf undestTypeName) defs =
        let tyArgs' = map rewriteFunType undestTypeArgs
            _returnTy = rewriteFunType undestReturnType
            instantiatedCtors = map ((`SystF.tyInstantiateN` tyArgs') . snd) constructors
            branches = zipWith (handleBranches undestCasesExtra) instantiatedCtors undestCases
         in dest $
              UnDestMeta
                { undestTypeArgs = tyArgs',
                  -- , undestReturnType = returnTy
                  undestCases = branches,
                  undestCasesExtra = [],
                  ..
                }
    --
    -- f (SystF.Free (TermSig name) `SystF.App` args)
    --   | name `S.member` dtorsNames = SystF.Free (TermSig name) `SystF.App` (prefix' <> branches')
    --   where
    --     (branches, prefix) = reverse *** reverse $ span SystF.isArg $ reverse args
    --     tyArgErr tyArg = error $ show name <> ": unexpected TyArg " <> renderSingleLineStr (pretty tyArg)
    --     prefix' = closurifyTyArgs prefix
    --     branches' = SystF.argElim tyArgErr (SystF.TermArg . rewriteHofBody . rewriteNestedLamArgs) <$> branches
    f x = x

    handleBranches :: [Arg lang] -> Type lang -> Term lang -> Term lang
    handleBranches exc (SystF.TyFun _ tyB) (SystF.Lam ann ty t) =
      SystF.Lam ann (rewriteFunType ty) $ replaceApply (applyFunName ty) $ handleBranches exc tyB t
    handleBranches exc _ t = t `SystF.appN` exc

-- * Defunctionalization of functions

defunFuns ::
  (LanguagePretty lang, Pretty (FunDef lang), LanguageBuiltins lang) =>
  PrtUnorderedDefs lang ->
  (PrtUnorderedDefs lang, M.Map Name (HofsList lang))
defunFuns defs = runWriter $ traverseDefs defunFunDef defs
  where
    defunFunDef name (DFunDef FunDef {..}) = do
      when changed $ tell $ M.singleton name hofs
      pure $ DFunDef $ FunDef funIsRec funBody' funTy'
      where
        (funTy', hofs) = rewriteHofType funTy
        changed = funTy' /= funTy
        funBody'
          | changed = rewriteHofBody funBody
          | otherwise = funBody
    defunFunDef _ x = pure x

-- * Closure type generation

mkClosureTypes :: (Language lang) => [ClosureCtorInfo lang] -> Decls lang
mkClosureTypes infos = M.fromList $ typeDecls <> ctorDecls <> dtorDecls
  where
    types = M.toList $ M.fromListWith (<>) [(closureTypeName $ hofType $ hofArgInfo info, [info]) | info <- infos]
    typeDecls =
      [ ((TypeNamespace, tyName), typeDecl)
        | (tyName, infos') <- types,
          let info2ctor ClosureCtorInfo {..} = (ctorName, foldr SystF.TyFun (SystF.Free (TySig tyName) `SystF.TyApp` []) ctorArgs),
          let typeDecl = DTypeDef $ Datatype SystF.KStar [] (dtorName tyName) (info2ctor <$> sortOn ctorIdx infos')
      ]
    ctorDecls =
      [ ((TermNamespace, ctorName), DConstructor ctorIdx $ closureTypeName hofType)
        | ClosureCtorInfo {hofArgInfo = DefunHofArgInfo {..}, ..} <- infos
      ]
    dtorDecls = [((TermNamespace, dtorName tyName), DDestructor tyName) | tyName <- fst <$> types]

dtorName :: Name -> Name
dtorName tyName = [i|match_#{tyName}|]

-- * Apply function generation

mkApplyFuns :: (Language lang) => [ClosureCtorInfo lang] -> Decls lang
mkApplyFuns infos = M.fromList funDecls
  where
    funs = M.toList $ M.fromListWith (<>) [(applyFunName $ hofType $ hofArgInfo info, [info]) | info <- infos]

    funDecls =
      [ ((TermNamespace, funName), DFunDef $ FunDef NonRec funBody funTy)
        | (funName, infos') <- funs,
          let infos'' = sortOn ctorIdx infos',
          let DefunHofArgInfo {..} = hofArgInfo $ head infos'',
          let closTy = closureType hofType,
          let funTy = closTy `SystF.TyFun` hofType,
          let funBody =
                let closArgIdx = SystF.TermArg $ SystF.Bound (SystF.Ann "cls") 0 `SystF.App` []
                    dtorResTy = SystF.TyArg hofType
                    dtor = SystF.Free (TermSig $ dtorName $ closureTypeName hofType)
                 in SystF.Lam (SystF.Ann "cls") closTy $ dtor `SystF.App` (closArgIdx : dtorResTy : (SystF.TermArg . mkDtorBranch <$> infos''))
      ]
    mkDtorBranch ClosureCtorInfo {..} = foldr (SystF.Lam (SystF.Ann "ctx")) hofTerm ctorArgs

-- * Defunctionalization of function call sites

newtype DefunState lang = DefunState
  { closureType2Idx :: M.Map (B.Type lang) Int
  }
  deriving (Show)

data ClosureCtorInfo lang = ClosureCtorInfo
  { hofArgInfo :: DefunHofArgInfo lang,
    ctorIdx :: Int,
    ctorName :: Name,
    ctorArgs :: [Type lang],
    hofTerm :: Term lang
  }
  deriving (Show)

type DefunCallsCtx lang = RWS () [ClosureCtorInfo lang] (DefunState lang)

defunCalls ::
  forall lang.
  (Language lang) =>
  M.Map Name (HofsList lang) ->
  PrtUnorderedDefs lang ->
  DefunCallsCtx lang (PrtUnorderedDefs lang)
defunCalls toDefun decls@PrtUnorderedDefs {..} = do
  decls' <- for prtUODecls $ \case
    DFunction r body ty -> (\body' -> DFunction r body' ty) <$> defunCallsInTerm [] body
    def -> pure def
  pure $ PrtUnorderedDefs decls'
  where
    defunCallsInTerm :: [(Type lang, SystF.Ann Name)] -> Term lang -> DefunCallsCtx lang (Term lang)
    defunCallsInTerm = go
      where
        go :: [(Type lang, SystF.Ann Name)] -> Term lang -> DefunCallsCtx lang (Term lang)
        go ctx (term `SystF.App` args) = do
          args' <- mapM (SystF.argElim (pure . SystF.TyArg) (fmap SystF.TermArg . go ctx)) args
          goApp ctx term args'
        go ctx (SystF.Lam ann ty term) = SystF.Lam ann ty <$> go ((ty, ann) : ctx) term
        go ctx (SystF.Abs ann k term) = SystF.Abs ann k <$> go ctx term

        -- If @name@ was previously detected as something that needs
        -- to be defunctionalized, lets do it!
        goApp ctx (SystF.Free (TermSig name)) args
          | Just hofsList <- M.lookup name toDefun = do
            args' <- forM (zip3 [0 ..] hofsList args) (replaceArg ctx)
            pure $ SystF.Free (TermSig name) `SystF.App` args'
          -- If not, the app in question might still be something like:
          -- > Just @(Integer -> Integer) (\(x : Integer) . x + 1)
          -- And that needs to be defun'ed too!
          -- WARNING: can't use prtDefOf here because we might be looking
          -- at partially defun'ed terms, so they'll have occurences of
          -- a still undefined _Apply!!... symbol
          | Just (DConstructor _ _) <- M.lookup (TermNamespace, name) prtUODecls = do
            let nameTy = runReader (typeOfIdent name) decls
            SystF.App (SystF.Free (TermSig name))
              <$> goNestedArgs ctx nameTy args
        goApp _ term args = pure $ term `SystF.App` args

        goNestedArgs ::
          [(Type lang, SystF.Ann Name)] ->
          Type lang ->
          [Arg lang] ->
          DefunCallsCtx lang [Arg lang]
        goNestedArgs _ _ [] = return []
        goNestedArgs ctx ty@SystF.TyAll {} (SystF.TyArg arg : args) = do
          -- We will recurse instantiating with the non-defun'ed type, so we know which
          -- arguments need to be defunctionalizaed because they will be of type TyFun!
          args' <- goNestedArgs ctx (SystF.tyInstantiate ty arg) args
          return $ SystF.TyArg (rewriteFunType arg) : args'
        goNestedArgs ctx (SystF.TyFun tyA tyB) (SystF.TermArg arg : args) = do
          arg' <- case tyA of
            SystF.TyFun {} -> defunCallsInTerm ctx arg >>= mkClosureArg ctx (DefunHofArgInfo tyA)
            _ -> return (SystF.TermArg arg)
          args' <- goNestedArgs ctx tyB args
          return (arg' : args')
        goNestedArgs ctx ty args =
          error $
            unlines
              [ "goNestedArgs: term application is either not well-typed or not eta-expanded",
                "ctx: " ++ show ctx,
                "ty: " ++ show (pretty ty),
                "args: " ++ show (pretty args)
              ]

    replaceArg ::
      [(Type lang, SystF.Ann Name)] ->
      (Integer, Maybe (DefunHofArgInfo lang), Arg lang) ->
      DefunCallsCtx lang (Arg lang)
    replaceArg ctx (_, Just hofArgInfo, SystF.TermArg lam@SystF.Lam {}) =
      defunCallsInTerm ctx lam >>= mkClosureArg ctx hofArgInfo
    replaceArg _ (_, _, arg) = pure arg

mkClosureArg ::
  forall lang.
  (LanguagePretty lang, LanguageBuiltins lang) =>
  [(Type lang, SystF.Ann Name)] ->
  DefunHofArgInfo lang ->
  Term lang ->
  DefunCallsCtx lang (Arg lang)
-- We hope that lam is already defunctionalized properly, no need to do anything
mkClosureArg _ DefunHofArgNested lam = pure (SystF.TermArg lam)
mkClosureArg ctx hofArgInfo@DefunHofArgInfo {..} lam = do
  ctorIdx <- newCtorIdx $ closureType hofType
  let ctorName = [i|#{closureTypeName hofType}_ctor_#{ctorIdx}|]

  let closureCtor =
        ClosureCtorInfo
          { hofArgInfo = hofArgInfo,
            ctorIdx = ctorIdx,
            ctorName = ctorName,
            ctorArgs = ctorArgs,
            hofTerm = remapFreeDeBruijns free2closurePos lam
          }
  tell [closureCtor]
  pure $ SystF.TermArg $ SystF.Free (TermSig ctorName) `SystF.App` [SystF.TermArg $ SystF.Bound (snd $ ctx !! fromIntegral idx) idx `SystF.App` [] | idx <- frees]
  where
    frees = collectFreeDeBruijns lam
    free2closurePos =
      M.fromList
        [ (freeIdx, closurePos)
          | freeIdx <- frees
          | closurePos <- reverse [0 .. fromIntegral $ length frees - 1]
        ]
    ctorArgs = fst . (ctx !!) . fromIntegral <$> frees

collectFreeDeBruijns ::
  Term lang ->
  [Integer]
collectFreeDeBruijns = nub . go 0
  where
    go cutoff (SystF.App var args) = checkVar cutoff var <> foldMap (SystF.argElim (const mempty) (go cutoff)) args
    go cutoff (SystF.Lam _ _ term) = go (cutoff + 1) term
    go cutoff (SystF.Abs _ _ term) = go (cutoff + 1) term

    checkVar cutoff (SystF.Bound _ n) | n >= cutoff = [n - cutoff]
    checkVar _ _ = mempty

remapFreeDeBruijns ::
  M.Map Integer Integer ->
  Term lang ->
  Term lang
remapFreeDeBruijns mapping = go 0
  where
    go cutoff (SystF.App var args) = remapVar cutoff var `SystF.App` (SystF.argElim SystF.TyArg (SystF.TermArg . go cutoff) <$> args)
    go cutoff (SystF.Lam ann ty term) = SystF.Lam ann ty $ go (cutoff + 1) term
    go cutoff (SystF.Abs ann k term) = SystF.Abs ann k $ go (cutoff + 1) term

    remapVar cutoff (SystF.Bound _ n) | n >= cutoff = SystF.Bound (SystF.Ann "ctx") $ cutoff + mapping M.! (n - cutoff)
    remapVar _ v = v

newCtorIdx :: LanguageBuiltins lang => B.Type lang -> DefunCallsCtx lang Int
newCtorIdx ty = do
  idx <- gets $ M.findWithDefault 0 ty . closureType2Idx
  modify' $ \st -> st {closureType2Idx = M.insert ty (idx + 1) $ closureType2Idx st}
  pure idx

-- * Defunctionalization of function definitions

-- TODO: rename to 'HOArgPos' and give example; the idea being
-- that @[Nothing, Just (HofArg "Int -> Bool"), Nothing]@ gives us info
-- that we need to defunctionalize the second argument to a function expecting
-- three arguments
type HofsList lang = [Maybe (DefunHofArgInfo lang)]

traverseDefs ::
  Monad m =>
  (Name -> Definition lang -> m (Definition lang)) ->
  PrtUnorderedDefs lang ->
  m (PrtUnorderedDefs lang)
traverseDefs f defs = do
  decls' <- forM defsList $ \(name@(_, inner), def) -> (name,) <$> f inner def
  pure $ defs {prtUODecls = M.fromList decls'}
  where
    defsList = M.toList $ prtUODecls defs

data DefunHofArgInfo lang
  = DefunHofArgInfo {hofType :: B.Type lang}
  | -- | This is not necessarily an argument we have to defunctionalize, because the closure appears
    --  nested as a potential argument to another type, but we do have to rewrite the
    --  type definition!
    DefunHofArgNested
  deriving (Show, Eq, Ord)

-- Changes the type of the form @Ty1 -> (Ty2 -> Ty3) -> Ty4@ to @Ty1 -> Closure[Ty2->Ty3] -> Ty4@
-- where the @Closure[Ty2->Ty3]@ is the ADT with the labels and environments for the funargs of type @Ty2 -> Ty3@.
rewriteHofType ::
  forall lang.
  (Language lang) =>
  B.Type lang ->
  (B.Type lang, HofsList lang)
rewriteHofType = go 0
  where
    go :: Integer -> B.Type lang -> (B.Type lang, [Maybe (DefunHofArgInfo lang)])
    go pos (dom `SystF.TyFun` cod) = (dom' `SystF.TyFun` cod', posApply : applies)
      where
        (cod', applies) = go (pos + 1) cod
        (dom', posApply) =
          case dom of
            SystF.TyFun {} -> (closureType dom, Just $ DefunHofArgInfo dom)
            ty | SystF.tyHasFuns ty -> (rewriteFunType ty, Just DefunHofArgNested)
            _ -> (dom, Nothing)
    go _ ty@SystF.TyApp {}
      | SystF.tyHasFuns ty = (rewriteFunType ty, [])
      | otherwise = (ty, [])
    go pos (SystF.TyAll ann k ty) = SystF.TyAll ann k *** (Nothing :) $ go (pos + 1) ty
    go _pos SystF.TyLam {} = error "unexpected arg type" -- TODO mention the type

-- | This is a little more eager than 'rewriteHofType', in this case, we rewrite ALL
-- function types.
rewriteFunType :: (Language lang) => B.Type lang -> B.Type lang
rewriteFunType = transform go
  where
    go ty@SystF.TyFun {} = closureType ty
    go x = x

-- Assumes the body is normalized enough so that all the binders are at the front.
-- Dis-assuming this is merely about recursing on `App` ctor as well.
rewriteHofBody ::
  (LanguagePretty lang, LanguageBuiltins lang) =>
  B.Term lang ->
  B.Term lang
rewriteHofBody = go
  where
    go e@SystF.App {} = e
    go (SystF.Abs ann kd body) = SystF.Abs ann kd $ go body
    go (SystF.Lam ann ty body) = case ty of
      SystF.TyFun {} -> SystF.Lam ann (closureType ty) $ replaceApply (applyFunName ty) $ go body
      _ -> SystF.Lam ann ty $ go body

replaceApply :: Name -> B.Term lang -> B.Term lang
replaceApply applyFun = go 0
  where
    go idx (SystF.Lam ann ty body) = SystF.Lam ann ty $ go (idx + 1) body
    go idx (SystF.Abs ann kd body) = SystF.Abs ann kd $ go (idx + 1) body
    go idx (SystF.App var args)
      | SystF.Bound _ n <- var,
        n == idx,
        not $ null args =
        SystF.App (SystF.Free (TermSig applyFun)) (SystF.TermArg (SystF.App var []) : args')
      | otherwise = SystF.App var args'
      where
        args' = recurArg <$> args
        recurArg arg@SystF.TyArg {} = arg
        recurArg (SystF.TermArg arg) = SystF.TermArg $ go idx arg

closureTypeName :: (LanguagePretty lang, LanguageBuiltins lang) => B.Type lang -> Name
closureTypeName ty = [i|Closure!!#{funTyStr ty}|]

applyFunName :: (LanguagePretty lang, LanguageBuiltins lang) => B.Type lang -> Name
applyFunName ty = [i|_Apply!!#{funTyStr ty}|]

closureType :: (LanguagePretty lang, LanguageBuiltins lang) => B.Type lang -> B.Type lang
closureType ty = SystF.Free (TySig $ closureTypeName ty) `SystF.TyApp` []

funTyStr :: (LanguagePretty lang, LanguageBuiltins lang) => B.Type lang -> T.Text
funTyStr (dom `SystF.TyFun` cod) = funTyStr dom <> "_" <> funTyStr cod
funTyStr app@SystF.TyApp {} = argsToStr [app]
funTyStr ty =
  error $
    "unexpected arg type during defunctionalization:\n"
      <> renderSingleLineStr (pretty ty)
-}
