{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE LambdaCase #-}

module Pirouette.Transformations.Defunctionalization(defunctionalize) where

import Control.Arrow ((***))
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Data.Bifunctor
import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.String
import Data.String.Interpolate.IsString
import qualified Data.Text as T
import Data.Void
import Prettyprinter hiding (Pretty, pretty)

import Debug.Trace

import Pirouette.Monad
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.Base as B
import Pirouette.Term.Syntax.Pretty
import Pirouette.Term.Syntax.Subst
import Pirouette.Term.Syntax.SystemF

import Pirouette.Transformations.Utils

defunctionalize :: (PrettyLang lang, Pretty (FunDef lang Name), LanguageDef lang)
                => PrtUnorderedDefs lang
                -> PrtUnorderedDefs lang
defunctionalize = etaExpand -- traceDefsId $ defunDefs defs0

etaExpand :: forall lang. (PrettyLang lang, Pretty (FunDef lang Name), LanguageDef lang)
          => PrtUnorderedDefs lang
          -> PrtUnorderedDefs lang
etaExpand defs@PrtUnorderedDefs{..} = transformBi exp defs
  where
    exp :: PrtTerm lang -> PrtTerm lang
    exp src@(F (FreeName name) `App` args)
      | Just nameType <- lookupNameType prtUODecls name
      , specNameType <- nameType `appN` argsTy
      , (fullArgs, _) <- flattenType specNameType
      , remainingArgs <- drop (length args - length argsTy) fullArgs
      , let remArgsLen = fromIntegral $ length remainingArgs
      , remArgsLen > 0
      , let new = wrapInLambdas remainingArgs $ F (FreeName name) `App` ((shiftArg remArgsLen <$> args) <> mkExpIndices remArgsLen)
        = trace ("was: " <> renderSingleLineStr (pretty src))
        . trace ("got: " <> renderSingleLineStr (pretty new))
        $ new
      where 
        argsTy = mapMaybe fromTyArg args
    exp term = term

    mkExpIndices cnt = [ Arg $ B (Ann "η") idx `App` []
                       | idx <- reverse [0 .. cnt - 1]
                       ]

wrapInLambdas :: [FlatArgType lang] -> PrtTerm lang -> PrtTerm lang
wrapInLambdas types term = foldr f term types
  where
    f (FlatTyArg k) = Abs (Ann "η") k
    f (FlatTermArg ty) = Lam (Ann "η") ty

data FlatArgType lang
  = FlatTyArg Kind
  | FlatTermArg (PrtType lang)
  deriving (Show)

flattenType :: PrtType lang -> ([FlatArgType lang], PrtType lang)
flattenType ty@TyApp{} = ([], ty)
flattenType (dom `TyFun` cod) = first (FlatTermArg dom :) $ flattenType cod
flattenType (TyAll ann kind ty) = first (FlatTyArg kind :) $ flattenType ty
flattenType TyLam{} = error "unnormalized type"

-- TODO have a proper @instance HasSubst (PrtArg lang)@ or smth similar
shiftArg :: Integer -> PrtArg lang -> PrtArg lang
shiftArg k (Arg e) = Arg $ shift k e
shiftArg k (TyArg t) = TyArg $ shift k t

-- * Returns the type of the given name.
--
-- This may return Nothing if the name is not known or
-- if the name doesn't have a *-inhabiting type (for instance, being a type itself).
lookupNameType :: Decls lang Name -> Name -> Maybe (PrtType lang)
lookupNameType decls name = name `M.lookup` decls >>= getName
  where
    getName (DFunDef fd) = Just $ funTy fd
    getName (DConstructor idx typeName) = do
      DTypeDef Datatype{..} <- typeName `M.lookup` decls   -- this pattern-match failure shall probably be a hard error instead of Nothing
      conTy <- constructors `safeIdx` idx
      pure $ foldr (\(name, kind) ty -> TyAll (Ann name) kind ty) (snd conTy) typeVariables
    getName (DDestructor na) = Nothing -- TODO just write the type of the destructor out
    getName (DTypeDef td) = Nothing

defunDefs :: forall lang. (PrettyLang lang, LanguageDef lang) => PrtUnorderedDefs lang -> PrtUnorderedDefs lang
defunDefs defs = defs { prtUODecls = defunDef <$> prtUODecls defs }
  where
    defunDef :: Definition lang Name -> Definition lang Name
    defunDef (DFunDef fd) = DFunDef $ defunFun fd
    defunDef (DTypeDef td) = DTypeDef td
    defunDef x = x

    defunFun :: FunDef lang Name -> FunDef lang Name
    defunFun FunDef{..} = let (ty', hofs) = rewriteHofType funTy
                           in (if ty' /= funTy
                                 then trace ("was: " <> renderSingleLineStr (pretty funTy))
                                    . trace ("got: " <> renderSingleLineStr (pretty ty'))
                                    . trace ("var: " <> show hofs)
                                    . trace ("body was: " <> renderSingleLineStr (pretty funBody))
                                    . trace ("body got: " <> renderSingleLineStr (pretty $ rewriteHofBody hofs funBody))
                                 else id)
                              FunDef{..}

data PosApply lang = PosApply
  { synthType :: B.Type lang Name
  , applyFunName :: Name
  } deriving (Show)

-- Changes the type of the form @Ty1 -> (Ty2 -> Ty3) -> Ty4@ to @Ty1 -> Closure[Ty2->Ty3] -> Ty4@
-- where the @Closure[Ty2->Ty3]@ is the ADT with the labels and environments for the funargs of type @Ty2 -> Ty3@.
rewriteHofType :: forall lang. (PrettyLang lang, LanguageDef lang)
               => B.Type lang Name
               -> (B.Type lang Name, [Maybe (PosApply lang)])
rewriteHofType = go 0
  where
    go :: Integer -> B.Type lang Name -> (B.Type lang Name, [Maybe (PosApply lang)])
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
                           in (synthType, Just PosApply{..})
               _ -> (dom, Nothing)
    go _    ty@TyApp{} = (ty, []) -- this doesn't defun things like `List (foo -> bar)`, which is fine for now
    go pos (TyAll ann k ty) = TyAll ann k *** (Nothing :) $ go (pos + 1) ty
    go pos (TyLam ann k ty) = error "unexpected arg type" -- TODO mention the type

-- Assumes the body is normalized enough so that all the binders are at the front.
rewriteHofBody :: (PrettyLang lang, LanguageDef lang)
               => [Maybe (PosApply lang)]
               -> B.Term lang Name
               -> B.Term lang Name
rewriteHofBody = go
  where
    go [] term = term
    go _ App{} = error "unexpected App, arguments not exhausted yet"

    go (Nothing : rest) (Lam ann ty body) = Lam ann ty $ go rest body
    go (Nothing : rest) (Abs ann kd body) = Abs ann kd $ go rest body

    go (Just PosApply{..} : rest) (Lam ann ty body) = Lam ann synthType $ replaceApply applyFunName $ go rest body
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
