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
import Data.Generics.Uniplate.Data
import qualified Data.IntMap as IM
import Data.List (nub)
import qualified Data.Map as M
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

defunctionalize :: (PrettyLang lang, Pretty (FunDef lang Name), LanguageDef lang)
                => PrtUnorderedDefs lang
                -> PrtUnorderedDefs lang
defunctionalize defs = traceDefsId $ defunCalls toDefun $ etaExpand defs'
  where
    (defs', toDefun) = defunDefs defs

-- * Defunctionalization of function call sites

newtype DefunState lang = DefunState
  { closureType2Idx :: M.Map (B.Type lang Name) Int
  }
  deriving (Show)

type DefunBodiesCtx lang = RWS () () (DefunState lang)

defunCalls :: forall lang. (PrettyLang lang, LanguageDef lang)
           => M.Map Name (HofsList lang)
           -> PrtUnorderedDefs lang
           -> PrtUnorderedDefs lang
defunCalls toDefun defs = fst $ evalRWS (defunCallsM defs) () (DefunState mempty)
  where
    defunCallsM :: PrtUnorderedDefs lang -> DefunBodiesCtx lang (PrtUnorderedDefs lang)
    defunCallsM PrtUnorderedDefs{..} = do
      mainTerm' <- defunCallsInTerm prtUOMainTerm
      decls' <- for prtUODecls $ \case DFunction r body ty -> (\body' -> DFunction r body' ty) <$> defunCallsInTerm body
                                       def -> pure def
      pure $ PrtUnorderedDefs decls' mainTerm'

    defunCallsInTerm :: PrtTerm lang -> DefunBodiesCtx lang (PrtTerm lang)
    defunCallsInTerm = go []
      where
        go :: [(FlatArgType lang, Ann Name)] -> PrtTerm lang -> DefunBodiesCtx lang (PrtTerm lang)
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
               -> DefunBodiesCtx lang (PrtArg lang)
    replaceArg ctx (_, Just hofArgInfo, Arg lam@Lam {}) = mkClosureArg ctx hofArgInfo lam
    replaceArg _   (_, _, arg) = pure arg

mkClosureArg :: LanguageDef lang
             => [(FlatArgType lang, Ann Name)]
             -> DefunHofArgInfo lang
             -> PrtTerm lang
             -> DefunBodiesCtx lang (PrtArg lang)
mkClosureArg ctx DefunHofArgInfo{..} lam = do
  ctorIdx <- newCtorIdx synthType
  let ctorName = [i|#{closureTypeName}_ctor_#{ctorIdx}|]
  pure $ Arg $ F (FreeName ctorName) `App` [ Arg $ B (snd $ ctx !! fromIntegral idx) idx `App` [] | idx <- frees ]
  where
    frees = collectFreeDeBruijns lam
    free2closurePos = M.fromList [ (freeIdx, closurePos)
                                 | freeIdx <- frees
                                 | closurePos <- reverse [0 .. fromIntegral $ length frees - 1]
                                 ]

collectFreeDeBruijns :: PrtTerm lang
                     -> [Integer]
collectFreeDeBruijns = nub . go 0
  where
    go cutoff (App var args) = checkVar cutoff var <> foldMap (argElim (const mempty) (go cutoff)) args
    go cutoff (Lam _ _ term) = go (cutoff + 1) term
    go cutoff (Abs _ _ term) = go (cutoff + 1) term

    checkVar cutoff (B _ n) | n >= cutoff = [n - cutoff]
    checkVar _ _ = mempty

newCtorIdx :: LanguageDef lang => B.Type lang Name -> DefunBodiesCtx lang Int
newCtorIdx ty = do
  idx <- gets $ M.findWithDefault 0 ty . closureType2Idx
  modify' $ \st -> st { closureType2Idx = M.insert ty (idx + 1) $ closureType2Idx st }
  pure idx

-- * Defunctionalization of function definitions

type HofsList lang = [Maybe (DefunHofArgInfo lang)]

defunDefs :: forall lang. (PrettyLang lang, LanguageDef lang) => PrtUnorderedDefs lang -> (PrtUnorderedDefs lang, M.Map Name (HofsList lang))
defunDefs defs = (defs { prtUODecls = decls' }, M.fromList toDefun)
  where
    (toDefun, decls') = M.mapAccumWithKey f [] $ prtUODecls defs
    f toDefunAcc name def
      | Just hofsList <- maybeHofsList = ((name, hofsList) : toDefunAcc, def')
      | otherwise = (toDefunAcc, def)
      where
        (def', maybeHofsList) = defunDef def

    defunDef :: Definition lang Name -> (Definition lang Name, Maybe (HofsList lang))
    defunDef (DFunDef fd) = first DFunDef $ defunFun fd
    defunDef (DTypeDef td) = (DTypeDef td, Nothing) -- TODO do this too
    defunDef x = (x, Nothing)

    defunFun :: FunDef lang Name -> (FunDef lang Name, Maybe (HofsList lang))
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
  { synthType :: B.Type lang Name
  , closureTypeName :: Name
  , applyFunName :: Name
  } deriving (Show)

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
               TyFun{} -> let tyStr = funTyStr dom
                              closureTypeName = [i|Closure[#{tyStr}]|]
                              applyFunName = [i|Apply[#{tyStr}]|]
                              synthType = TyApp (F $ TyFree closureTypeName) []
                           in (synthType, Just DefunHofArgInfo{..})
               _ -> (dom, Nothing)
    go _    ty@TyApp{} = (ty, []) -- this doesn't defun things like `List (foo -> bar)`, which is fine for now
    go pos (TyAll ann k ty) = TyAll ann k *** (Nothing :) $ go (pos + 1) ty
    go pos (TyLam ann k ty) = error "unexpected arg type" -- TODO mention the type

-- Assumes the body is normalized enough so that all the binders are at the front.
rewriteHofBody :: (PrettyLang lang, LanguageDef lang)
               => [Maybe (DefunHofArgInfo lang)]
               -> B.Term lang Name
               -> B.Term lang Name
rewriteHofBody = go
  where
    go [] term = term
    go _ App{} = error "unexpected App, arguments not exhausted yet"

    go (Nothing : rest) (Lam ann ty body) = Lam ann ty $ go rest body
    go (Nothing : rest) (Abs ann kd body) = Abs ann kd $ go rest body

    go (Just DefunHofArgInfo{..} : rest) (Lam ann ty body) = Lam ann synthType $ replaceApply applyFunName $ go rest body
    go (Just _ : _) Abs{} = error "unexpected Abs where a type should've been replaced"

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

funTyStr :: (PrettyLang lang, LanguageDef lang) => B.Type lang Name -> T.Text
funTyStr (dom `TyFun` cod) = funTyStr dom <> " => " <> funTyStr cod
funTyStr app@TyApp{} = argsToStr [app]
funTyStr ty = error $ "unexpected arg type during defunctionalization:\n"
                   <> renderSingleLineStr (pretty ty)
