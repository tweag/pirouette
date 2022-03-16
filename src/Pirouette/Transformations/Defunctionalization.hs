{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TupleSections #-}

module Pirouette.Transformations.Defunctionalization(defunctionalize) where

import Control.Arrow ((***))
import Control.Monad.RWS.Strict
import Data.Bifunctor (first, second)
import Data.Generics.Uniplate.Data
import qualified Data.IntMap as IM
import Data.List (nub)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.String.Interpolate.IsString
import qualified Data.Text as T
import Data.Traversable

import Debug.Trace

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base as B
import Pirouette.Term.Syntax.SystemF

import Pirouette.Transformations.EtaExpand
import Pirouette.Transformations.Utils
import Control.Monad.Writer.Strict

defunctionalize :: (PrettyLang lang, Pretty (FunDef lang Name), LanguageDef lang)
                => PrtUnorderedDefs lang
                -> PrtUnorderedDefs lang
defunctionalize defs = traceDefsId defs' { prtUODecls = prtUODecls defs' <> typeDecls <> applyFunDecls }
  where
    (defs', closureCtorInfos) = evalRWS (defunFuns >=> defunTypes $ etaExpand defs) mempty (DefunState mempty)

    typeDecls = mkClosureTypes closureCtorInfos
    applyFunDecls = mkApplyFuns closureCtorInfos

-- * Defunctionalization of types

-- evalRWS (defunCallsM defs) mempty (DefunState mempty)
defunTypes :: (PrettyLang lang, LanguageDef lang)
           => PrtUnorderedDefs lang
           -> DefunCallsCtx lang (PrtUnorderedDefs lang)
defunTypes defs = defunCalls toDefun defs'
  where
    (defs', toDefun) = runWriter $ traverseDefs defunTypeDef defs

    defunTypeDef name (DTypeDef Datatype{..}) = do
      forM_ allMaybeHofs $ \case (ctorName, Just hof) -> tell $ M.singleton ctorName hof
                                 _ -> pure ()
      pure $ DTypeDef Datatype{constructors = ctors', ..}
      where
        (ctors', allMaybeHofs) = unzip [ ((ctorName, ctorTy'), (ctorName, maybeHofs))
                                       | (ctorName, ctorTy) <- constructors
                                       , let (ctorTy', hofs) = rewriteHofType ctorTy
                                             maybeHofs | ctorTy' == ctorTy = Nothing
                                                       | otherwise = trace ("ctor " <> show ctorName)
                                                                   . trace ("was: " <> renderSingleLineStr (pretty ctorTy))
                                                                   . trace ("got: " <> renderSingleLineStr (pretty ctorTy'))
                                                                   $ Just hofs
                                       ]
    defunTypeDef _ x = pure x

-- Destructors have a well-known structure: they are η-expanded,
-- they accept a bunch of funargs that needn't be defunctionalized, etc,
-- so we can have a few shortcuts
defunDtors :: forall lang. (PrettyLang lang, LanguageDef lang)
           => PrtUnorderedDefs lang
           -> PrtUnorderedDefs lang
defunDtors defs = transformBi f defs
  where
    dtorsNames = S.fromList $ mapMaybe getDtorName (M.elems $ prtUODecls defs)
    getDtorName (DTypeDef Datatype{..}) = Just destructor
    getDtorName _ = Nothing

    f :: PrtTerm lang -> PrtTerm lang
    f (F (FreeName name) `App` args)
      | name `S.member` dtorsNames = F (FreeName name) `App` (prefix <> branches')
      where
        (branches, prefix) = reverse *** reverse $ span isArg $ reverse args
        tyArgErr tyArg = error $ show name <> ": unexpected TyArg " <> renderSingleLineStr (pretty tyArg)
        branches' = argElim tyArgErr (Arg . rewriteHofBody) <$> branches
    f x = x

-- * Defunctionalization of functions

defunFuns :: (PrettyLang lang, Pretty (FunDef lang Name), LanguageDef lang)
          => PrtUnorderedDefs lang
          -> DefunCallsCtx lang (PrtUnorderedDefs lang)
defunFuns defs = defunCalls toDefun defs'
  where
    (defs', toDefun) = defunDefs defs

-- * Closure type generation

mkClosureTypes :: (PrettyLang lang, LanguageDef lang) => [ClosureCtorInfo lang] -> Decls lang Name
mkClosureTypes infos = M.fromList $ typeDecls <> ctorDecls <> dtorDecls
  where
    types = M.toList $ M.fromListWith (<>) [ (closureTypeName $ hofType $ hofArgInfo info, [info]) | info <- infos ]
    typeDecls = [ (tyName, typeDecl)
                | (tyName, infos) <- types
                , let info2ctor ClosureCtorInfo{..} = (ctorName, foldr TyFun (F (TyFree tyName) `TyApp` []) ctorArgs)
                , let typeDecl = DTypeDef $ Datatype KStar [] (dtorName tyName) (info2ctor <$> infos)
                ]
    ctorDecls = [ (ctorName, DConstructor ctorIdx $ closureTypeName hofType)
                | info@ClosureCtorInfo { hofArgInfo = DefunHofArgInfo{..}, ..} <- infos
                ]
    dtorDecls = [ (dtorName tyName, DDestructor tyName) | tyName <- fst <$> types ]

dtorName :: Name -> Name
dtorName tyName = [i|#{tyName}_match|]

-- * Apply function generation

mkApplyFuns :: (PrettyLang lang, LanguageDef lang) => [ClosureCtorInfo lang] -> Decls lang Name
mkApplyFuns infos = M.fromList funDecls
  where
    funs = M.toList $ M.fromListWith (<>) [ (applyFunName $ hofType $ hofArgInfo info, [info]) | info <- infos ]

    funDecls = [ (funName, DFunDef $ FunDef NonRec funBody funTy)
               | (funName, infos) <- funs
               , let DefunHofArgInfo{..} = hofArgInfo $ head infos
               , let closTy = closureType hofType
               , let funTy = closTy `TyFun` hofType
               , let (argsTys, resTy) = flattenType hofType
               , let funBody = let closArgIdx = Arg $ B (Ann "cls") 0 `App` []
                                   dtorResTy = TyArg resTy
                                   dtor = F (FreeName $ dtorName $ closureTypeName hofType)
                                in Lam (Ann "cls") closTy $ dtor `App` (closArgIdx : dtorResTy : (Arg . mkDtorBranch <$> infos))
               ]
    mkDtorBranch ClosureCtorInfo{..} = foldr (Lam (Ann "ctx")) hofTerm ctorArgs

-- * Defunctionalization of function call sites

newtype DefunState lang = DefunState
  { closureType2Idx :: M.Map (B.Type lang Name) Int
  }
  deriving (Show)

data ClosureCtorInfo lang = ClosureCtorInfo
  { hofArgInfo :: DefunHofArgInfo lang
  , ctorIdx :: Int
  , ctorName :: Name
  , ctorArgs :: [PrtType lang]
  , hofTerm :: PrtTerm lang
  }

type DefunCallsCtx lang = RWS () [ClosureCtorInfo lang] (DefunState lang)

defunCalls :: forall lang. (PrettyLang lang, LanguageDef lang)
           => M.Map Name (HofsList lang)
           -> PrtUnorderedDefs lang
           -> DefunCallsCtx lang (PrtUnorderedDefs lang)
defunCalls toDefun PrtUnorderedDefs{..} = do
  mainTerm' <- defunCallsInTerm prtUOMainTerm
  decls' <- for prtUODecls $ \case DFunction r body ty -> (\body' -> DFunction r body' ty) <$> defunCallsInTerm body
                                   def -> pure def
  pure $ PrtUnorderedDefs decls' mainTerm'
  where
    defunCallsInTerm :: PrtTerm lang -> DefunCallsCtx lang (PrtTerm lang)
    defunCallsInTerm = go []
      where
        go :: [(FlatArgType lang, Ann Name)] -> PrtTerm lang -> DefunCallsCtx lang (PrtTerm lang)
        go ctx (term `App` args) = do
          args' <- mapM (argElim (pure . TyArg) (fmap Arg . go ctx)) args
          goApp ctx term args'
        go ctx (Lam ann ty term) = Lam ann ty <$> go ((FlatTermArg ty, ann) : ctx) term
        go ctx (Abs ann k  term) = Abs ann k  <$> go ((FlatTyArg k, ann) : ctx) term

        goApp ctx (F (FreeName name)) args
          | Just hofsList <- M.lookup name toDefun = do
            args' <- forM (zip3 [0..] hofsList args) (replaceArg ctx)
            pure $ F (FreeName name) `App` args'
        goApp ctx term args = pure $ term `App` args

    replaceArg :: [(FlatArgType lang, Ann Name)]
               -> (Integer, Maybe (DefunHofArgInfo lang), PrtArg lang)
               -> DefunCallsCtx lang (PrtArg lang)
    replaceArg ctx (_, Just hofArgInfo, Arg lam@Lam {}) = mkClosureArg ctx hofArgInfo lam
    replaceArg _   (_, _, arg) = pure arg

mkClosureArg :: (PrettyLang lang, LanguageDef lang)
             => [(FlatArgType lang, Ann Name)]
             -> DefunHofArgInfo lang
             -> PrtTerm lang
             -> DefunCallsCtx lang (PrtArg lang)
mkClosureArg ctx hofArgInfo@DefunHofArgInfo{..} lam = do
  ctorIdx <- newCtorIdx $ closureType hofType
  let ctorName = [i|#{closureTypeName hofType}_ctor_#{ctorIdx}|]
  tell [ClosureCtorInfo{hofTerm = remapFreeDeBruijns free2closurePos lam, ..}]
  pure $ Arg $ F (FreeName ctorName) `App` [ Arg $ B (snd $ ctx !! fromIntegral idx) idx `App` [] | idx <- frees ]
  where
    frees = collectFreeDeBruijns lam
    free2closurePos = M.fromList [ (freeIdx, closurePos)
                                 | freeIdx <- frees
                                 | closurePos <- reverse [0 .. fromIntegral $ length frees - 1]
                                 ]
    ctorArgs = (\(FlatTermArg ty) -> ty) . fst . (ctx !!) . fromIntegral <$> frees

collectFreeDeBruijns :: PrtTerm lang
                     -> [Integer]
collectFreeDeBruijns = nub . go 0
  where
    go cutoff (App var args) = checkVar cutoff var <> foldMap (argElim (const mempty) (go cutoff)) args
    go cutoff (Lam _ _ term) = go (cutoff + 1) term
    go cutoff (Abs _ _ term) = go (cutoff + 1) term

    checkVar cutoff (B _ n) | n >= cutoff = [n - cutoff]
    checkVar _ _ = mempty

remapFreeDeBruijns :: M.Map Integer Integer
                   -> PrtTerm lang
                   -> PrtTerm lang
remapFreeDeBruijns mapping = go 0
  where
    go cutoff (App var args) = remapVar cutoff var `App` (argElim TyArg (Arg . go cutoff) <$> args)
    go cutoff (Lam ann ty term) = Lam ann ty $ go (cutoff + 1) term
    go cutoff (Abs ann k  term) = Abs ann k  $ go (cutoff + 1) term

    remapVar cutoff (B _ n) | n >= cutoff = B (Ann "ctx") $ cutoff + mapping M.! (n - cutoff)
    remapVar _ v = v

newCtorIdx :: LanguageDef lang => B.Type lang Name -> DefunCallsCtx lang Int
newCtorIdx ty = do
  idx <- gets $ M.findWithDefault 0 ty . closureType2Idx
  modify' $ \st -> st { closureType2Idx = M.insert ty (idx + 1) $ closureType2Idx st }
  pure idx

-- * Defunctionalization of function definitions

type HofsList lang = [Maybe (DefunHofArgInfo lang)]

traverseDefs :: Monad m
             => (Name -> Definition lang Name -> m (Definition lang Name))
             -> PrtUnorderedDefs lang
             -> m (PrtUnorderedDefs lang)
traverseDefs defunDef defs = do
  decls' <- forM defsList $ \(name, def) -> (name,) <$> defunDef name def
  pure $ defs { prtUODecls = M.fromList decls' }
  where
    defsList = M.toList $ prtUODecls defs

defunDefs :: forall lang. (PrettyLang lang, LanguageDef lang)
          => PrtUnorderedDefs lang
          -> (PrtUnorderedDefs lang, M.Map Name (HofsList lang))
defunDefs = runWriter . traverseDefs defunDef
  where
    defunDef name (DFunDef FunDef{..}) =  do
      when changed $ tell $ M.singleton name hofs
      pure $ DFunDef $ FunDef funIsRec funBody' funTy'
      where
        (funTy', hofs) = rewriteHofType funTy
        changed = funTy' /= funTy
        funBody' | changed = rewriteHofBody funBody
                 | otherwise = funBody
    defunDef _ x = pure x

newtype DefunHofArgInfo lang = DefunHofArgInfo { hofType :: B.Type lang Name } deriving (Show, Eq, Ord)

-- Changes the type of the form @Ty1 -> (Ty2 -> Ty3) -> Ty4@ to @Ty1 -> Closure[Ty2->Ty3] -> Ty4@
-- where the @Closure[Ty2->Ty3]@ is the ADT with the labels and environments for the funargs of type @Ty2 -> Ty3@.
rewriteHofType :: forall lang. (PrettyLang lang, LanguageDef lang)
               => B.Type lang Name
               -> (B.Type lang Name, HofsList lang)
rewriteHofType = go 0
  where
    go :: Integer -> B.Type lang Name -> (B.Type lang Name, [Maybe (DefunHofArgInfo lang)])
    go pos (dom `TyFun` cod) = (dom' `TyFun` cod', posApply : applies)
      where
        (cod', applies) = go (pos + 1) cod
        thisIdx = App (B (Ann "") pos) []
        (dom', posApply) =
          case dom of
               TyFun{} -> (closureType dom, Just $ DefunHofArgInfo dom)
               _ -> (dom, Nothing)
    go _    ty@TyApp{} = (ty, []) -- this doesn't defun things like `List (foo -> bar)`, which is fine for now
    go pos (TyAll ann k ty) = TyAll ann k *** (Nothing :) $ go (pos + 1) ty
    go pos (TyLam ann k ty) = error "unexpected arg type" -- TODO mention the type

-- Assumes the body is normalized enough so that all the binders are at the front.
-- Dis-assuming this is merely about recursing on `App` ctor as well.
rewriteHofBody :: (PrettyLang lang, LanguageDef lang)
               => B.Term lang Name
               -> B.Term lang Name
rewriteHofBody = go
  where
    go e@App{} = e
    go (Abs ann kd body) = Abs ann kd $ go body
    go (Lam ann ty body) = case ty of
                                TyFun{} -> Lam ann (closureType ty) $ replaceApply (applyFunName ty) $ go body
                                _ -> Lam ann ty $ go body

replaceApply :: Name -> B.Term lang Name -> B.Term lang Name
replaceApply applyFunName = go 0
  where
    go idx (Lam ann ty body) = Lam ann ty $ go (idx + 1) body
    go idx (Abs ann kd body) = Abs ann kd $ go (idx + 1) body
    go idx (App var args)
      | B _ n <- var
      , n == idx
      , not $ null args = App (F (FreeName applyFunName)) (Arg (App var []) : args')
      | otherwise = App var args'
      where
        args' = recurArg <$> args
        recurArg arg@TyArg{} = arg
        recurArg (Arg arg) = Arg $ go idx arg

closureTypeName :: (PrettyLang lang, LanguageDef lang) => B.Type lang Name -> Name
closureTypeName ty = [i|Closure[#{funTyStr ty}]|]

applyFunName :: (PrettyLang lang, LanguageDef lang) => B.Type lang Name -> Name
applyFunName ty = [i|Apply[#{funTyStr ty}]|]

closureType :: (PrettyLang lang, LanguageDef lang) => B.Type lang Name -> B.Type lang Name
closureType ty = F (TyFree $ closureTypeName ty) `TyApp` []

funTyStr :: (PrettyLang lang, LanguageDef lang) => B.Type lang Name -> T.Text
funTyStr (dom `TyFun` cod) = funTyStr dom <> " => " <> funTyStr cod
funTyStr app@TyApp{} = argsToStr [app]
funTyStr ty = error $ "unexpected arg type during defunctionalization:\n"
                   <> renderSingleLineStr (pretty ty)
