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

import Control.Arrow ((***))
import Control.Monad.RWS.Strict
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
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base as B
import qualified Pirouette.Term.Syntax.SystemF as SystF
import Pirouette.Transformations.EtaExpand
import Pirouette.Transformations.Utils
import Pirouette.Transformations.Monomorphization (hofsClosure, findPolyHOFDefs)

-- Defunctionalization assumes lots of things! Namelly:
--
-- 1. No polymorphic higher-order function occurence
-- 2. everything has been fully eta-expanded
-- 3. ??? still discovering

defunctionalize :: (Language lang, LanguageBuiltinTypes lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
defunctionalize defs =
  case defunctionalizeAssumptions defs of
    () -> defs' {prtUODecls = prtUODecls defs' <> typeDecls <> applyFunDecls}
  where
    (defs', closureCtorInfos) = evalRWS (defunFuns >=> defunTypes $ etaExpandAll defs) mempty (DefunState mempty)

    typeDecls = mkClosureTypes closureCtorInfos
    applyFunDecls = mkApplyFuns closureCtorInfos

defunctionalizeAssumptions :: (Language lang) => PrtUnorderedDefs lang -> ()
defunctionalizeAssumptions defs = either error (const ()) . traverseDefs (\n d -> defOk n d >> return d) $ defs
  where
    dtorsNames = S.fromList $ mapMaybe getDtorName (M.elems $ prtUODecls defs)
    getDtorName (DTypeDef Datatype {..}) = Just destructor
    getDtorName _ = Nothing

    hofs = hofsClosure (prtUODecls defs) (findPolyHOFDefs $ prtUODecls defs)

    defOk :: forall lang . (Language lang) => Name -> Definition lang -> Either String ()
    defOk n (DFunDef FunDef {..}) =
      let termAbs = [ t | t@SystF.Abs {} <- universe funBody ]

          tyArgs :: [ Arg lang ]
          tyArgs = [ thisTyArgs | (SystF.App (SystF.Free (TermSig t)) args) <- universe funBody
                       , t `S.notMember` dtorsNames
                       , thisTyArgs <- filter SystF.isTyArg args
                       , not $ null thisTyArgs ]

          tyVars :: [ Var lang ]
          tyVars = [ t | t@(SystF.Bound _ _) <- universeBi funTy ]
       in if n `M.member` hofs
          then if null termAbs && null tyArgs && null tyVars
            then Right ()
            else Left $ "Defunctionalization will fail for: " ++ show n ++ "\n"
                     ++ show termAbs ++ show tyArgs ++ show tyVars
          else Right ()
    defOk _ _ = return ()

-- * Defunctionalization of types

defunTypes ::
  (LanguagePretty lang, LanguageBuiltins lang) =>
  PrtUnorderedDefs lang ->
  DefunCallsCtx lang (PrtUnorderedDefs lang)
defunTypes defs = defunCalls toDefun $ defunDtors defs'
  where
    (defs', toDefun) = runWriter $ traverseDefs defunTypeDef defs

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
    dtorsNames = S.fromList $ mapMaybe getDtorName (M.elems $ prtUODecls defs)
    getDtorName (DTypeDef Datatype {..}) = Just destructor
    getDtorName _ = Nothing

    f :: Term lang -> Term lang
    f (SystF.Free (TermSig name) `SystF.App` args)
      | name `S.member` dtorsNames = SystF.Free (TermSig name) `SystF.App` (prefix <> branches')
      where
        (branches, prefix) = reverse *** reverse $ span SystF.isArg $ reverse args
        tyArgErr tyArg = error $ show name <> ": unexpected TyArg " <> renderSingleLineStr (pretty tyArg)
        branches' = SystF.argElim tyArgErr (SystF.TermArg . rewriteHofBody) <$> branches
    f x = x

-- * Defunctionalization of functions

defunFuns ::
  (LanguagePretty lang, Pretty (FunDef lang), LanguageBuiltins lang) =>
  PrtUnorderedDefs lang ->
  DefunCallsCtx lang (PrtUnorderedDefs lang)
defunFuns defs = defunCalls toDefun defs'
  where
    (defs', toDefun) = runWriter $ traverseDefs defunFunDef defs

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
      [ (tyName, typeDecl)
        | (tyName, infos') <- types,
          let info2ctor ClosureCtorInfo {..} = (ctorName, foldr SystF.TyFun (SystF.Free (TySig tyName) `SystF.TyApp` []) ctorArgs),
          let typeDecl = DTypeDef $ Datatype SystF.KStar [] (dtorName tyName) (info2ctor <$> sortOn ctorIdx infos')
      ]
    ctorDecls =
      [ (ctorName, DConstructor ctorIdx $ closureTypeName hofType)
        | ClosureCtorInfo {hofArgInfo = DefunHofArgInfo {..}, ..} <- infos
      ]
    dtorDecls = [(dtorName tyName, DDestructor tyName) | tyName <- fst <$> types]

dtorName :: Name -> Name
dtorName tyName = [i|match_#{tyName}|]

-- * Apply function generation

mkApplyFuns :: (Language lang) => [ClosureCtorInfo lang] -> Decls lang
mkApplyFuns infos = M.fromList funDecls
  where
    funs = M.toList $ M.fromListWith (<>) [(applyFunName $ hofType $ hofArgInfo info, [info]) | info <- infos]

    funDecls =
      [ (funName, DFunDef $ FunDef NonRec funBody funTy)
        | (funName, infos') <- funs,
          let DefunHofArgInfo {..} = hofArgInfo $ head infos',
          let closTy = closureType hofType,
          let funTy = closTy `SystF.TyFun` hofType,
          let funBody =
                let closArgIdx = SystF.TermArg $ SystF.Bound (SystF.Ann "cls") 0 `SystF.App` []
                    dtorResTy = SystF.TyArg hofType
                    dtor = SystF.Free (TermSig $ dtorName $ closureTypeName hofType)
                 in SystF.Lam (SystF.Ann "cls") closTy $ dtor `SystF.App` (closArgIdx : dtorResTy : (SystF.TermArg . mkDtorBranch <$> infos'))
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
  } deriving (Show)

type DefunCallsCtx lang = RWS () [ClosureCtorInfo lang] (DefunState lang)

defunCalls ::
  forall lang.
  (Language lang) =>
  M.Map Name (HofsList lang) ->
  PrtUnorderedDefs lang ->
  DefunCallsCtx lang (PrtUnorderedDefs lang)
defunCalls toDefun PrtUnorderedDefs {..} = do
  mainTerm' <- defunCallsInTerm prtUOMainTerm
  decls' <- for prtUODecls $ \case
    DFunction r body ty -> (\body' -> DFunction r body' ty) <$> defunCallsInTerm body
    def -> pure def
  pure $ PrtUnorderedDefs decls' mainTerm'
  where
    defunCallsInTerm :: Term lang -> DefunCallsCtx lang (Term lang)
    defunCallsInTerm = go []
      where
        go :: [(FlatArgType lang, SystF.Ann Name)] -> Term lang -> DefunCallsCtx lang (Term lang)
        go ctx (term `SystF.App` args) = do
          args' <- mapM (SystF.argElim (pure . SystF.TyArg) (fmap SystF.TermArg . go ctx)) args
          goApp ctx term args'
        go ctx (SystF.Lam ann ty term) = SystF.Lam ann ty <$> go ((FlatTermArg ty, ann) : ctx) term
        go ctx (SystF.Abs ann k term) = SystF.Abs ann k <$> go ((FlatTyArg k, ann) : ctx) term

        goApp ctx (SystF.Free (TermSig name)) args
          | Just hofsList <- M.lookup name toDefun = do
            args' <- forM (zip3 [0 ..] hofsList args) (replaceArg ctx)
            pure $ SystF.Free (TermSig name) `SystF.App` args'
        goApp _ term args = pure $ term `SystF.App` args

    replaceArg ::
      [(FlatArgType lang, SystF.Ann Name)] ->
      (Integer, Maybe (DefunHofArgInfo lang), Arg lang) ->
      DefunCallsCtx lang (Arg lang)
    replaceArg ctx (_, Just hofArgInfo, SystF.TermArg lam@SystF.Lam {}) = mkClosureArg ctx hofArgInfo lam
    replaceArg _ (_, _, arg) = pure arg


mkClosureArg ::
  (LanguagePretty lang, LanguageBuiltins lang) =>
  [(FlatArgType lang, SystF.Ann Name)] ->
  DefunHofArgInfo lang ->
  Term lang ->
  DefunCallsCtx lang (Arg lang)
mkClosureArg ctx hofArgInfo@DefunHofArgInfo {..} lam = do
  ctorIdx <- newCtorIdx $ closureType hofType
  let ctorName = [i|#{closureTypeName hofType}_ctor_#{ctorIdx}|]

  tell [ClosureCtorInfo {hofTerm = remapFreeDeBruijns free2closurePos lam, ..}]
  pure $ SystF.TermArg $ SystF.Free (TermSig ctorName) `SystF.App` [SystF.TermArg $ SystF.Bound (snd $ ctx !! fromIntegral idx) idx `SystF.App` [] | idx <- frees]
  where
    frees = collectFreeDeBruijns lam
    free2closurePos =
      M.fromList
        [ (freeIdx, closurePos)
          | freeIdx <- frees
          | closurePos <- reverse [0 .. fromIntegral $ length frees - 1]
        ]
    ctorArgs = (\(FlatTermArg ty) -> ty) . fst . (ctx !!) . fromIntegral <$> frees

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
  decls' <- forM defsList $ \(name, def) -> (name,) <$> f name def
  pure $ defs {prtUODecls = M.fromList decls'}
  where
    defsList = M.toList $ prtUODecls defs

newtype DefunHofArgInfo lang = DefunHofArgInfo {hofType :: B.Type lang} deriving (Show, Eq, Ord)

-- Changes the type of the form @Ty1 -> (Ty2 -> Ty3) -> Ty4@ to @Ty1 -> Closure[Ty2->Ty3] -> Ty4@
-- where the @Closure[Ty2->Ty3]@ is the ADT with the labels and environments for the funargs of type @Ty2 -> Ty3@.
rewriteHofType ::
  forall lang.
  (LanguagePretty lang, LanguageBuiltins lang) =>
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
            _ -> (dom, Nothing)
    go _ ty@SystF.TyApp {} = (ty, []) -- this doesn't defun things like `List (foo -> bar)`, which is fine for now
    go pos (SystF.TyAll ann k ty) = SystF.TyAll ann k *** (Nothing :) $ go (pos + 1) ty
    go _pos SystF.TyLam {} = error "unexpected arg type" -- TODO mention the type

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
