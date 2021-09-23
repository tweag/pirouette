{-# LANGUAGE FlexibleContexts #-}

module Pirouette.Term.Defunctionalize(defunctionalize) where

import           Pirouette.TLA.Syntax

import qualified Language.TLAPlus.Syntax as TLA
import qualified Language.TLAPlus.Parser as TLA

import           Control.Monad.State
import           Data.Data
import           Data.Foldable
import           Data.Generics.Uniplate.Operations
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import           Data.Sequence(Seq, (|>))

defunLabel :: Int -> Int -> TLA.AS_Expression
defunLabel arity idx = tlaString $ "defun_" <> show arity <> "_" <> show idx

applyFunIdent :: Int -> TLA.AS_Expression
applyFunIdent arity = tlaIdent $ "apply" <> show arity

applyFunArgs :: Int -> [TLA.AS_Expression]
applyFunArgs arity = [ tlaIdent $ "x" <> show n | n <- [1..arity] ]

data DefunClosureInfo = DefunClosureInfo
  { savedBody :: TLA.AS_Expression
  , freeVarNames :: S.Set String
  }

newtype DefunState = DefunState
  { defunDefs :: M.Map Int (Seq DefunClosureInfo)
  }

defunState0 :: DefunState
defunState0 = DefunState mempty

-- |Saves a function into the state for defunctionalization and returns its index
saveDefun :: (MonadState DefunState m)
          => Int
          -> TLA.AS_Expression
          -> S.Set String
          -> m Int
saveDefun arity fun freevars = do
  allFuns <- gets defunDefs
  let thisArityFuns = M.findWithDefault mempty arity allFuns
  modify' $ \st -> st { defunDefs = M.insert arity (thisArityFuns |> DefunClosureInfo fun freevars) allFuns }
  pure $ Seq.length thisArityFuns

funargNames :: [TLA.AS_QBoundN] -> [String]
funargNames = fmap (\(TLA.AS_QBoundN [TLA.AS_Ident _ [] name] _) -> name)

defunClosureLabel :: String
defunClosureLabel = "label"

genApply :: Int -> Seq DefunClosureInfo -> TLA.AS_UnitDef
genApply arity cases = tlaOpDef (applyFunIdent arity) (clos : args) $ TLA.AS_Case di arms Nothing
  where
    args = applyFunArgs arity
    arms = [ TLA.AS_CaseArm di (isIndex idx) (unwrapFunBody freevars expr)
           | (idx, DefunClosureInfo expr freevars) <- zip [0..] $ toList cases
           ]

    clos = tlaIdent "closure"
    isIndex idx = (clos `tlaProj'` defunClosureLabel) `tlaEq` defunLabel arity idx

    unwrapFunBody freevars (TLA.AS_QuantifierBoundFunction _ funargs expr) = transformBi (replaceArgs freevars (funargNames funargs)) expr
    unwrapFunBody _        expr = error $ "Unexpected expression: " <> show expr

    replaceArgs freevars funargs expr@(TLA.AS_Ident _ [] name)
      | Just val <- lookup name (zip funargs args) = val
      | name `S.member` freevars = clos `tlaProj'` name
      | otherwise = expr
    replaceArgs _        _       expr = expr

genApplies :: DefunState -> [TLA.AS_UnitDef]
genApplies st = uncurry genApply <$> M.toList (defunDefs st)

genAppliesFwdDecls :: DefunState -> [TLA.AS_UnitDef]
genAppliesFwdDecls st = genFwdDecl <$> M.keys (defunDefs st)
  where
    genFwdDecl arity = TLA.AS_RecursiveDecl diu [TLA.AS_OpHead (applyFunIdent arity) (replicate (1 + arity) $ tlaIdent "_")]

defunCtor :: (MonadState DefunState m)
          => TLA.AS_UnitDef
          -> m TLA.AS_UnitDef
defunCtor (TLA.AS_OperatorDef opinfo flag h@(TLA.AS_OpHead _ args) expr) = TLA.AS_OperatorDef opinfo flag h <$> goTree (vars args) expr
  where
    goTree inScope (TLA.AS_OpApp info expr args)
        = TLA.AS_OpApp info <$> goTree inScope expr <*> mapM (goTree inScope >=> defunArg inScope) args
    goTree inScope (TLA.AS_QuantifierBoundFunction info funargs expr)
        = TLA.AS_QuantifierBoundFunction info funargs <$> goTree (inScope <> S.fromList (funargNames funargs)) expr
    goTree inScope (TLA.AS_Lambda info funargs expr)
        = TLA.AS_Lambda info funargs <$> goTree (inScope <> vars funargs) expr
    goTree inScope expr = descendM (goTree inScope) expr

    defunArg inScope arg@(TLA.AS_QuantifierBoundFunction _ funargs expr) = do
      let arity = length funargs
      let freevars = inScope `S.intersection` vars expr
          varsMap = [ TLA.AS_MapTo (TLA.AS_Field var) (TLA.AS_Ident di [] var)
                    | var <- S.toList freevars
                    ]
      curIdx <- saveDefun arity arg freevars
      pure $ TLA.AS_RecordFunction di $ TLA.AS_MapTo (TLA.AS_Field defunClosureLabel) (defunLabel arity curIdx)
                                      : varsMap
    defunArg _ arg = pure arg

    vars :: Data ast => ast -> S.Set String
    vars ast = S.fromList [ name
                          | TLA.AS_Ident _ [] name <- universeBi ast
                          ]
defunCtor def = pure def

-- Note that this would also defunctionalize tuple accesses (of the form `tup[1]`),
-- since they are represented as function applications in the AST.
--
-- Since we only really need pairs for now,
-- the workaround is to access tuple elements via helper functions `fst`/`snd`
-- defined in the skeleton files.
defunDtor :: TLA.AS_UnitDef -> TLA.AS_UnitDef
defunDtor = transformBi f
  where
    f expr@(TLA.AS_InfixOP info TLA.AS_FunApp funExpr (TLA.AS_FunArgList _ args)) = tlaOpApp (applyFunIdent $ length args) (funExpr : args)
    f expr = expr

-- There are three main steps during defunctionalization:
-- * defunctionalizing constructors:
--   replacing any function being passed as an argument by the corresponding closure info
--   (basically a struct containing the function identifier along with any free variables).
--   As an example,
--   `Con([arg1 \in ArgTy1 |-> arg1 + freevar1 + freevar2], ...)`
--   gets replaced with
--   `Con([label |-> "some_unique_id", freevar1 |-> freevar1, freevar2 |-> freevar2], ...)`
-- * defunctionalizing destructors, or, rather, function applications:
--   any function application `f[arg1, ..., argN]` gets replaced with a call to `applyN`,
--   or, in particular, `applyN(f, arg1, ..., argN)`.
-- * generation of the `applyN` functions.
--
-- The order of first two steps matters:
-- transforming the AST to defunctionalize constructors means that the bodies of the corresponding functions
-- get replaced in the original AST, and since they might contain function applications,
-- they need to also be "destructor-defunctionalized".
-- So, if defunctionalizing destructors happens first, those applications also get transformed in one fell swoop.
-- Otherwise, the applyN function would have been had defunctionalized as well,
-- which just requires more extra steps.
--
-- As an example, consider `Con([arg1 \in ..., arg2 \in ... |-> arg1[arg2]])`.
-- Defunctionalizing destructors first yields `Con([arg1 \in ..., arg2 \in ... |-> apply1(arg1, arg2)])`
-- which then gets replaced by `Con([label |-> "some_unique_label"])` with
-- apply2(label, arg1, arg2) == CASE label = "some_unique_label" -> apply1(arg1, arg2)
--
-- If, on the other hand, we did defunctionalize ctors first and didn't pay attention to
-- defunctionalize function applications in function bodies stashed away for the applyN function,
-- we could've ended up with
-- apply2(label, arg1, arg2) == CASE label = "some_unique_label" -> arg1[arg2]
-- which is incorrect.
defunctionalize :: [TLA.AS_UnitDef] -> [TLA.AS_UnitDef]
defunctionalize defs = genAppliesFwdDecls st
                    <> defs''
                    <> genApplies st
  where
    defs' = defunDtor <$> defs
    (defs'', st) = runState (mapM defunCtor defs') defunState0

