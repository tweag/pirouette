{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

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
                                    . trace ("body got: " <> renderSingleLineStr (pretty $ rewriteHofBody hofs funBody))
                                 else id)
                              FunDef{..}

data SubstIndex = SubstIndex
  deriving (Show)

data PosApply lang = PosApply
  { applyArg :: PrtArg lang
  , synthType :: Either SubstIndex (B.Type lang Name)
  } deriving (Show)

-- Changes the type of the form @Ty1 -> (Ty2 -> Ty3) -> Ty4@ to @Ty1 -> Closure[Ty2->Ty3] -> Ty4@
-- where the @Closure[Ty2->Ty3]@ is the ADT with the labels and environments for the funargs of type @Ty2 -> Ty3@.
rewriteHofType :: forall lang. (PrettyLang lang, LanguageDef lang)
               => B.Type lang Name
               -> (B.Type lang Name, [PosApply lang])
rewriteHofType = go 0
  where
    go :: Integer -> B.Type lang Name -> (B.Type lang Name, [PosApply lang])
    go pos (dom `TyFun` cod) = (dom' `TyFun` cod', PosApply{ synthType = Right dom', .. } : applies)
      where
        (cod', applies) = go (pos + 1) cod
        thisIdx = App (B (Ann "") pos) []
        (dom', applyArg) =
          case dom of
               TyFun{} -> let tyStr = funTyStr dom
                              closureTypeName = [i|Closure[#{tyStr}]|]
                              applyFunName = [i|Apply[#{tyStr}]|]
                           in (TyApp (F $ TyFree closureTypeName) [], Arg $ App (F (FreeName applyFunName)) [Arg thisIdx])
               _ -> (dom, Arg thisIdx)
    go _    ty@TyApp{} = (ty, []) -- this doesn't defun things like `List (foo -> bar)`, which is fine for now
    go pos (TyAll ann k ty) = TyAll ann k *** (PosApply{..} :) $ go (pos + 1) ty
      where
        synthType = Left SubstIndex
        applyArg = TyArg $ TyApp (B (Ann "") pos) []
    go pos (TyLam ann k ty) = error "unexpected arg type" -- TODO mention the type

-- Assumes the body is normalized enough so that all the binders are at the front.
rewriteHofBody :: forall lang. (PrettyLang lang, LanguageDef lang)
               => [PosApply lang]
               -> B.Term lang Name
               -> B.Term lang Name
rewriteHofBody [] body = body
rewriteHofBody applies body =
  body `appN` [ applyArg
              | (PosApply{..}, idx) <- zip applies [0..]
              ]

funTyStr :: (PrettyLang lang, LanguageDef lang) => B.Type lang Name -> T.Text
funTyStr (dom `TyFun` cod) = funTyStr dom <> " => " <> funTyStr cod
funTyStr app@TyApp{} = argsToStr [app]
funTyStr ty = error $ "unexpected arg type during defunctionalization:\n"
                   <> renderSingleLineStr (pretty ty)
