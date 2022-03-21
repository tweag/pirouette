{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}

module Pirouette.Transformations.Defunctionalization(defunctionalize) where

import Control.Arrow ((***))
import Control.Monad.RWS.Strict
import Data.Bifunctor (first)
import Data.List (nub)
import qualified Data.Map as M
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

defunctionalize :: (LanguagePretty lang, LanguageBuiltins lang)
                => PrtUnorderedDefs lang
                -> PrtUnorderedDefs lang
defunctionalize defs = renderSingleLineStr (pretty typeDecls) `trace` defs'' { prtUODecls = prtUODecls defs'' <> typeDecls <> applyFunDecls }
  where
    (defs', toDefun) = defunDefs defs
    (defs'', closureCtorInfos) = defunCalls toDefun $ etaExpandAll defs'

    typeDecls = mkClosureTypes closureCtorInfos
    applyFunDecls = mkApplyFuns closureCtorInfos

-- * Closure type generation

mkClosureTypes :: [ClosureCtorInfo lang] -> Decls lang
mkClosureTypes infos = M.fromList $ typeDecls <> ctorDecls <> dtorDecls
  where
    types = M.toList $ M.fromListWith (<>) [ (closureTypeName $ hofArgInfo info, [info]) | info <- infos ]
    typeDecls = [ (tyName, typeDecl)
                | (tyName, infos) <- types
                , let info2ctor ClosureCtorInfo{..} = (ctorName, foldr TyFun (Free (B.TySig tyName) `TyApp` []) ctorArgs)
                , let typeDecl = DTypeDef $ Datatype KStar [] (dtorName tyName) (info2ctor <$> infos)
                ]
    ctorDecls = [ (ctorName, DConstructor ctorIdx closureTypeName)
                | info@ClosureCtorInfo { hofArgInfo = DefunHofArgInfo{..}, ..} <- infos
                ]
    dtorDecls = [ (dtorName tyName, DDestructor tyName) | tyName <- fst <$> types ]

dtorName :: Name -> Name
dtorName tyName = [i|#{tyName}_match|]

-- * Apply function generation

mkApplyFuns :: [ClosureCtorInfo lang] -> Decls lang
mkApplyFuns infos = M.fromList funDecls
  where
    funs = M.toList $ M.fromListWith (<>) [ (applyFunName $ hofArgInfo info, [info]) | info <- infos ]

    funDecls = [ (funName, DFunDef $ FunDef NonRec funBody funTy)
               | (funName, infos) <- funs
               , let DefunHofArgInfo{..} = hofArgInfo $ head infos
               , let closTy = Free (B.TySig closureTypeName) `TyApp` []
               , let funTy = closTy `TyFun` hofType
               , let (argsTys, resTy) = flattenType hofType
               , let funBody = let closArgIdx = TermArg $ Bound (Ann "cls") 0 `App` []
                                   dtorResTy = TyArg resTy
                                in Lam (Ann "cls") closTy
                                    $ Free (B.TermSig $ dtorName closureTypeName) `App` (closArgIdx : dtorResTy : (TermArg . mkDtorBranch <$> infos))
               ]
    mkDtorBranch ClosureCtorInfo{..} = foldr (Lam (Ann "ctx")) hofTerm ctorArgs

-- * Defunctionalization of function call sites

newtype DefunState lang = DefunState
  { closureType2Idx :: M.Map (B.Type lang) Int
  }
  deriving (Show)

data ClosureCtorInfo lang = ClosureCtorInfo
  { hofArgInfo :: DefunHofArgInfo lang
  , ctorIdx :: Int
  , ctorName :: Name
  , ctorArgs :: [Type lang]
  , hofTerm :: Term lang
  }

type DefunBodiesCtx lang = RWS () [ClosureCtorInfo lang] (DefunState lang)

defunCalls :: forall lang. (LanguagePretty lang, LanguageBuiltins lang)
           => M.Map Name (HofsList lang)
           -> PrtUnorderedDefs lang
           -> (PrtUnorderedDefs lang, [ClosureCtorInfo lang])
defunCalls toDefun defs = evalRWS (defunCallsM defs) mempty (DefunState mempty)
  where
    defunCallsM :: PrtUnorderedDefs lang -> DefunBodiesCtx lang (PrtUnorderedDefs lang)
    defunCallsM PrtUnorderedDefs{..} = do
      mainTerm' <- defunCallsInTerm prtUOMainTerm
      decls' <- for prtUODecls $ \case DFunction r body ty -> (\body' -> DFunction r body' ty) <$> defunCallsInTerm body
                                       def -> pure def
      pure $ PrtUnorderedDefs decls' mainTerm'

    defunCallsInTerm :: Term lang -> DefunBodiesCtx lang (Term lang)
    defunCallsInTerm = go []
      where
        go :: [(FlatArgType lang, Ann Name)] -> Term lang -> DefunBodiesCtx lang (Term lang)
        go ctx (term `App` args) = do
          args' <- mapM (argElim (pure . TyArg) (fmap TermArg . go ctx)) args
          goApp ctx term args'
        go ctx (Lam ann ty term) = Lam ann ty <$> go ((FlatTermArg ty, ann) : ctx) term
        go ctx (Abs ann k  term) = Abs ann k  <$> go ((FlatTyArg k, ann) : ctx) term

        goApp ctx (Free (TermSig name)) args
          | Just hofsList <- M.lookup name toDefun = do
            args' <- forM (zip3 [0..] hofsList args) (replaceArg ctx)
            pure $ Free (B.TermSig name) `App` args'
        goApp ctx term args = pure $ term `App` args

    replaceArg :: [(FlatArgType lang, Ann Name)]
               -> (Integer, Maybe (DefunHofArgInfo lang), B.Arg lang)
               -> DefunBodiesCtx lang (B.Arg lang)
    replaceArg ctx (_, Just hofArgInfo, TermArg lam@Lam {}) = mkClosureArg ctx hofArgInfo lam
    replaceArg _   (_, _, arg) = pure arg

mkClosureArg :: LanguageBuiltins lang
             => [(FlatArgType lang, Ann Name)]
             -> DefunHofArgInfo lang
             -> Term lang
             -> DefunBodiesCtx lang (B.Arg lang)
mkClosureArg ctx hofArgInfo@DefunHofArgInfo{..} lam = do
  ctorIdx <- newCtorIdx synthType
  let ctorName = [i|#{closureTypeName}_ctor_#{ctorIdx}|]
  tell [ClosureCtorInfo{hofTerm = remapFreeDeBruijns free2closurePos lam, ..}]
  pure $ TermArg $ Free (B.TermSig ctorName) `App` [ TermArg $ Bound (snd $ ctx !! fromIntegral idx) idx `App` [] | idx <- frees ]
  where
    frees = collectFreeDeBruijns lam
    free2closurePos = M.fromList [ (freeIdx, closurePos)
                                 | freeIdx <- frees
                                 | closurePos <- reverse [0 .. fromIntegral $ length frees - 1]
                                 ]
    ctorArgs = (\(FlatTermArg ty) -> ty) . fst . (ctx !!) . fromIntegral <$> frees

collectFreeDeBruijns :: Term lang
                     -> [Integer]
collectFreeDeBruijns = nub . go 0
  where
    go cutoff (App var args) = checkVar cutoff var <> foldMap (argElim (const mempty) (go cutoff)) args
    go cutoff (Lam _ _ term) = go (cutoff + 1) term
    go cutoff (Abs _ _ term) = go (cutoff + 1) term

    checkVar cutoff (Bound _ n) | n >= cutoff = [n - cutoff]
    checkVar _ _ = mempty

remapFreeDeBruijns :: M.Map Integer Integer
                   -> Term lang
                   -> Term lang
remapFreeDeBruijns mapping = go 0
  where
    go cutoff (App var args) = remapVar cutoff var `App` (argElim TyArg (TermArg . go cutoff) <$> args)
    go cutoff (Lam ann ty term) = Lam ann ty $ go (cutoff + 1) term
    go cutoff (Abs ann k  term) = Abs ann k  $ go (cutoff + 1) term

    remapVar cutoff (Bound _ n) | n >= cutoff = Bound (Ann "ctx") $ cutoff + mapping M.! (n - cutoff)
    remapVar _ v = v

newCtorIdx :: LanguageBuiltins lang => B.Type lang -> DefunBodiesCtx lang Int
newCtorIdx ty = do
  idx <- gets $ M.findWithDefault 0 ty . closureType2Idx
  modify' $ \st -> st { closureType2Idx = M.insert ty (idx + 1) $ closureType2Idx st }
  pure idx

-- * Defunctionalization of function definitions

type HofsList lang = [Maybe (DefunHofArgInfo lang)]

defunDefs :: forall lang. (LanguagePretty lang, LanguageBuiltins lang) => PrtUnorderedDefs lang -> (PrtUnorderedDefs lang, M.Map Name (HofsList lang))
defunDefs defs = (defs { prtUODecls = decls' }, M.fromList toDefun)
  where
    (toDefun, decls') = M.mapAccumWithKey f [] $ prtUODecls defs
    f toDefunAcc name def
      | Just hofsList <- maybeHofsList = ((name, hofsList) : toDefunAcc, def')
      | otherwise = (toDefunAcc, def)
      where
        (def', maybeHofsList) = defunDef def

    defunDef :: Definition lang -> (Definition lang, Maybe (HofsList lang))
    defunDef (DFunDef fd) = first DFunDef $ defunFun fd
    defunDef (DTypeDef td) = (DTypeDef td, Nothing) -- TODO do this too
    defunDef x = (x, Nothing)

    defunFun :: FunDef lang -> (FunDef lang, Maybe (HofsList lang))
    defunFun FunDef{..} = dumpChange (FunDef funIsRec funBody' funTy' , hofsList)
      where
        (funTy', hofs) = rewriteHofType funTy
        changed = funTy' /= funTy
        funBody' | changed = rewriteHofBody hofs funBody
                 | otherwise = funBody
        dumpChange | changed = trace ("was: " <> renderSingleLineStr (pretty funTy))
                             . trace ("got: " <> renderSingleLineStr (pretty funTy'))
                             . trace ("var: " <> show hofs)
                             . trace ("body was: " <> renderSingleLineStr (pretty funBody))
                             . trace ("body got: " <> renderSingleLineStr (pretty $ rewriteHofBody hofs funBody))
                   | otherwise = id
        hofsList | changed = Just hofs
                 | otherwise = Nothing

data DefunHofArgInfo lang = DefunHofArgInfo
  { synthType :: B.Type lang
  , closureTypeName :: Name
  , applyFunName :: Name
  , hofType :: B.Type lang
  } deriving (Show, Eq, Ord)

-- Changes the type of the form @Ty1 -> (Ty2 -> Ty3) -> Ty4@ to @Ty1 -> Closure[Ty2->Ty3] -> Ty4@
-- where the @Closure[Ty2->Ty3]@ is the ADT with the labels and environments for the funargs of type @Ty2 -> Ty3@.
rewriteHofType :: forall lang. (LanguagePretty lang, LanguageBuiltins lang)
               => B.Type lang
               -> (B.Type lang, HofsList lang)
rewriteHofType = go 0
  where
    go :: Integer -> B.Type lang -> (B.Type lang, [Maybe (DefunHofArgInfo lang)])
    go pos (dom `TyFun` cod) = (dom' `TyFun` cod', posApply : applies)
      where
        (cod', applies) = go (pos + 1) cod
        thisIdx = App (Bound (Ann "") pos) []
        (dom', posApply) =
          case dom of
               TyFun{} -> let tyStr = funTyStr dom
                              closureTypeName = [i|Closure[#{tyStr}]|]
                              applyFunName = [i|Apply[#{tyStr}]|]
                              synthType = TyApp (Free $ B.TySig closureTypeName) []
                           in (synthType, Just DefunHofArgInfo{hofType = dom, ..})
               _ -> (dom, Nothing)
    go _    ty@TyApp{} = (ty, []) -- this doesn't defun things like `List (foo -> bar)`, which is fine for now
    go pos (TyAll ann k ty) = TyAll ann k *** (Nothing :) $ go (pos + 1) ty
    go pos (TyLam ann k ty) = error "unexpected arg type" -- TODO mention the type

-- Assumes the body is normalized enough so that all the binders are at the front.
rewriteHofBody :: (LanguagePretty lang, LanguageBuiltins lang)
               => [Maybe (DefunHofArgInfo lang)]
               -> B.Term lang
               -> B.Term lang
rewriteHofBody = go
  where
    go [] term = term
    go _ App{} = error "unexpected App, arguments not exhausted yet"

    go (Nothing : rest) (Lam ann ty body) = Lam ann ty $ go rest body
    go (Nothing : rest) (Abs ann kd body) = Abs ann kd $ go rest body

    go (Just DefunHofArgInfo{..} : rest) (Lam ann ty body) = Lam ann synthType $ replaceApply applyFunName $ go rest body
    go (Just _ : _) Abs{} = error "unexpected Abs where a type should've been replaced"

replaceApply :: Name -> B.Term lang -> B.Term lang
replaceApply applyFunName = go 0
  where
    go idx (Lam ann ty body) = Lam ann ty $ go (idx + 1) body
    go idx (Abs ann kd body) = Abs ann kd $ go (idx + 1) body
    go idx (App var args)
      | Bound _ n <- var
      , n == idx
      , not $ null args = App (Free (B.TermSig applyFunName)) (TermArg (App var []) : args')
      | otherwise = App var args'
      where
        args' = recurArg <$> args
        recurArg arg@TyArg{} = arg
        recurArg (TermArg arg) = TermArg $ go idx arg

funTyStr :: (LanguagePretty lang, LanguageBuiltins lang) => B.Type lang -> T.Text
funTyStr (dom `TyFun` cod) = funTyStr dom <> " => " <> funTyStr cod
funTyStr a@TyApp{} = argsToStr [a]
funTyStr ty = error $ "unexpected arg type during defunctionalization:\n"
                   <> renderSingleLineStr (pretty ty)
