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
defunctionalize defs0 = defunDefs defs0

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
                                    . trace ("body got: " <> renderSingleLineStr (pretty $ rewriteHofBodyArgTypes hofs funBody))
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
rewriteHofBodyArgTypes :: forall lang. (PrettyLang lang, LanguageDef lang)
                       => [Maybe (PosApply lang)]
                       -> B.Term lang Name
                       -> B.Term lang Name
rewriteHofBodyArgTypes [] = id
rewriteHofBodyArgTypes (Nothing : rest) =
  \case Lam ann ty body -> Lam ann ty $ rewriteHofBodyArgTypes rest body
        Abs ann kd body -> Abs ann kd $ rewriteHofBodyArgTypes rest body
        App{} -> error "unexpected App, arguments not exhausted yet"
rewriteHofBodyArgTypes (Just PosApply{..} : rest) =
  \case Lam ann ty body -> Lam ann synthType $ rewriteHofBodyArgTypes rest body
        Abs ann kd body -> error "unexpected Abs where a type should've been replaced"
        App{} -> error "unexpected App, arguments not exhausted yet"

funTyStr :: (PrettyLang lang, LanguageDef lang) => B.Type lang Name -> T.Text
funTyStr (dom `TyFun` cod) = funTyStr dom <> " => " <> funTyStr cod
funTyStr app@TyApp{} = argsToStr [app]
funTyStr ty = error $ "unexpected arg type during defunctionalization:\n"
                   <> renderSingleLineStr (pretty ty)
