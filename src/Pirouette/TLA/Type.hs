{-# LANGUAGE TypeFamilies #-}
module Pirouette.TLA.Type where

import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax.Subst
import Pirouette.Term.Syntax
import Pirouette.PlutusIR.ToTerm

import qualified PlutusCore as P

import           Control.Arrow (first)
import           Data.List (foldl')
import           Prettyprinter hiding (Pretty, pretty)
import           Data.String

-- |When translating a term to TLA, we will declare said term with
-- a given TLA type.
data TlaType
  -- |Represents polymorphism and is mostly ignored, its there just to make sure
  -- we can reuse bound variables from PirType
  = TlaAll (R.Ann Name) R.Kind TlaType
  -- |A term with type 'TlaOp' will be translated to a TLA operator that
  -- receives a number of arguments and returns a /value/ of the given 'PirType'
  | TlaOp   [TlaType] PirType
  -- |A term with type 'TlaTyOp' will be translated to a TLA operator that
  -- receives a number of arguments and returns a /set/ of values of the given 'PirType'
  | TlaTyOp [TlaType] PirType
    -- |Represents a TLA value of the given type
  | TlaVal PirType
  -- |Represents a TLA set of the given type
  | TlaSet PirType
  deriving (Eq, Show)

tlaTySubst :: Sub PirType -> TlaType -> TlaType
tlaTySubst s (TlaAll t k body) = TlaAll t k (tlaTySubst (liftSub s) body)
tlaTySubst s (TlaOp ts res)    = TlaOp   (map (tlaTySubst s) ts) (subst s res)
tlaTySubst s (TlaTyOp ts res)  = TlaTyOp (map (tlaTySubst s) ts) (subst s res)
tlaTySubst s (TlaVal v)        = TlaVal (subst s v)
tlaTySubst s (TlaSet v)        = TlaSet (subst s v)

tlaTyApp :: TlaType -> PirType -> TlaType
tlaTyApp (TlaAll _ _ t) m = tlaTySubst (singleSub m) t
tlaTyApp _ _              = error "tlaTyApp: Can't apply to monomorphic types"

tlaTyAppN :: TlaType -> [PirType] -> TlaType
tlaTyAppN = foldl' tlaTyApp

tlaTyRet :: TlaType -> TlaType
tlaTyRet (TlaOp [x] r)          = TlaVal r
tlaTyRet (TlaOp (_:xs) r)       = TlaOp xs r
tlaTyRet r                      = r

tlaTyArgs :: TlaType -> [TlaType]
tlaTyArgs (TlaOp args r)           = args
tlaTyArgs ty                       = []

tlaTyDropAll :: TlaType -> TlaType
tlaTyDropAll (TlaAll _ _ t) = tlaTyDropAll t
tlaTyDropAll t = t

-- |Applies a free name to a number of ordered bound variables.
tyApp :: Name -> [(Name, R.Kind)] -> PirType
tyApp n vs = R.TyApp (R.F $ TyFree n)
           $ zipWith (\i (n, _) -> R.tyPure (R.B (R.Ann n) $ fromIntegral i)) (reverse [0 .. length vs - 1]) vs

-- |Builtin type of TLA naturals
tlaTyNat :: TlaType
tlaTyNat = TlaVal pirTyNat

tlaTyBool :: TlaType
tlaTyBool = TlaVal pirTyBool

tlaTyBS :: TlaType
tlaTyBS = TlaVal pirTyBS

tlaTyData :: TlaType
tlaTyData = TlaVal pirTyData

tlaTyUnit :: TlaType
tlaTyUnit = TlaVal pirTyUnit

pirTyNat :: PirType
pirTyNat = R.tyPure $ R.F $ TyBuiltin PIRTypeInteger

pirTyBool :: PirType
pirTyBool = R.tyPure $ R.F $ TyBuiltin PIRTypeBool

pirTyData :: PirType
pirTyData = R.tyPure $ R.F $ TyBuiltin PIRTypeData

pirTyBS :: PirType
pirTyBS = R.tyPure $ R.F $ TyBuiltin PIRTypeByteString

pirTyUnit :: PirType
pirTyUnit = R.tyPure $ R.F $ TyBuiltin PIRTypeUnit

pirTyList :: PIRType -> PirType
pirTyList a = R.tyPure $ R.F $ TyBuiltin (PIRTypeList $ Just a)

tlaAll :: [(Name, R.Kind)] -> TlaType -> TlaType
tlaAll = flip (foldr (\(n, k) t -> TlaAll (R.Ann n) k t))

returnType :: TlaType -> PirType
returnType (TlaAll _ _ t) = returnType t
returnType (TlaOp _ t) = t
returnType (TlaVal t) = t
returnType (TlaSet t) = t

arity :: TlaType -> Int
arity (TlaOp  xs _) = length xs
arity _             = 0

tlaOp :: [TlaType] -> PirType -> TlaType
tlaOp [] = TlaVal
tlaOp xs = TlaOp xs

toTlaOpType :: PirType -> TlaType
toTlaOpType (R.TyAll v k t) = TlaAll v k (toTlaOpType t)
toTlaOpType t               = uncurry tlaOp . first (map toTlaOpType) . R.tyFunArgs $ t

toTlaHdOpType :: PirType -> TlaType
toTlaHdOpType (R.TyAll v k t) = TlaAll v k (toTlaHdOpType t)
toTlaHdOpType t               = uncurry tlaOp . first (map TlaVal) . R.tyFunArgs $ t

tlaTyBuiltin :: P.DefaultFun -> TlaType
tlaTyBuiltin P.AddInteger            = TlaOp [tlaTyNat, tlaTyNat] pirTyNat
tlaTyBuiltin P.SubtractInteger       = TlaOp [tlaTyNat, tlaTyNat] pirTyNat
tlaTyBuiltin P.MultiplyInteger       = TlaOp [tlaTyNat, tlaTyNat] pirTyNat
tlaTyBuiltin P.DivideInteger         = TlaOp [tlaTyNat, tlaTyNat] pirTyNat
tlaTyBuiltin P.QuotientInteger       = TlaOp [tlaTyNat, tlaTyNat] pirTyNat
tlaTyBuiltin P.RemainderInteger      = TlaOp [tlaTyNat, tlaTyNat] pirTyNat
tlaTyBuiltin P.ModInteger            = TlaOp [tlaTyNat, tlaTyNat] pirTyNat
tlaTyBuiltin P.LessThanInteger       = TlaOp [tlaTyNat, tlaTyNat] pirTyBool
tlaTyBuiltin P.LessThanEqualsInteger = TlaOp [tlaTyNat, tlaTyNat] pirTyBool
tlaTyBuiltin P.EqualsInteger         = TlaOp [tlaTyNat, tlaTyNat] pirTyBool
tlaTyBuiltin P.AppendByteString      = TlaOp [tlaTyBS, tlaTyBS] pirTyBS
tlaTyBuiltin P.EqualsByteString      = TlaOp [tlaTyBS, tlaTyBS] pirTyBool
tlaTyBuiltin P.IfThenElse            =
  let a = R.Ann (fromString "a") in
  TlaAll a R.KStar $
    TlaOp [ tlaTyBool
          , TlaVal (R.tyPure $ R.B a 0)
          , TlaVal (R.tyPure $ R.B a 0)
          ] (R.tyPure $ R.B a 0)
tlaTyBuiltin P.Sha2_256             = TlaOp [tlaTyBS] pirTyBS
tlaTyBuiltin P.ConstrData           = TlaOp [tlaTyNat, TlaVal $ pirTyList PIRTypeData] pirTyData
tlaTyBuiltin P.MkNilData            = TlaOp [tlaTyUnit] (pirTyList PIRTypeData)
tlaTyBuiltin P.Trace                =
  let a = R.Ann (fromString "a") in
  TlaAll a R.KStar $
    TlaOp [tlaTyBS, TlaVal (R.tyPure $ R.B a 0)] (R.tyPure $ R.B a 0)
tlaTyBuiltin P.ChooseData           =
  let a = R.Ann (fromString "a") in
  TlaAll a R.KStar $
    TlaOp [ TlaVal (R.tyPure $ R.B a 0)
          , TlaVal (R.tyPure $ R.B a 0)
          , TlaVal (R.tyPure $ R.B a 0)
          , TlaVal (R.tyPure $ R.B a 0)
          , TlaVal (R.tyPure $ R.B a 0)
          , tlaTyData
          ] (R.tyPure $ R.B a 0)
tlaTyBuiltin P.ChooseList           =
  let a = R.Ann (fromString "a")
      b = R.Ann (fromString "b")
  in
  TlaAll a R.KStar $ TlaAll b R.KStar $
    TlaOp [ TlaVal (R.tyPure $ R.B a 1)
          , TlaVal (R.tyPure $ R.B a 1)
          -- We want a list of b,
          -- but since the 'PIRType' does not include variable,
          -- 'Nothing' is used to represent it.
          , TlaVal $ R.tyPure $ R.F $ TyBuiltin (PIRTypeList Nothing)
          ] (R.tyPure $ R.B a 1)
tlaTyBuiltin P.FstPair              =
  let a = R.Ann (fromString "a")
      b = R.Ann (fromString "b")
  in
  TlaAll a R.KStar $ TlaAll b R.KStar $
    -- We want a pair of a, b,
    -- but since the 'PIRType' does not include variable,
    -- 'Nothing' is used to represent it.
    TlaOp [ TlaVal $ R.tyPure $ R.F $ TyBuiltin (PIRTypePair Nothing Nothing)
          ] (R.tyPure $ R.B a 1)
tlaTyBuiltin P.SndPair              =
  let a = R.Ann (fromString "a")
      b = R.Ann (fromString "b")
  in
  TlaAll a R.KStar $ TlaAll b R.KStar $
    -- We want a pair of a, b,
    -- but since the 'PIRType' does not include variable,
    -- 'Nothing' is used to represent it.
    TlaOp [ TlaVal $ R.tyPure $ R.F $ TyBuiltin (PIRTypePair Nothing Nothing)
          ] (R.tyPure $ R.B b 0)
tlaTyBuiltin P.UnConstrData         =
  TlaOp [tlaTyData
        ] (R.tyPure $ R.F $ TyBuiltin (PIRTypePair (Just PIRTypeInteger)  (Just $ PIRTypeList (Just PIRTypeData))))
tlaTyBuiltin P.HeadList             =
  let a = R.Ann (fromString "a") in
  TlaAll a R.KStar $
    -- We want a list of a,
    -- but since the 'PIRType' does not include variable,
    -- 'Nothing' is used to represent it.
    TlaOp [ TlaVal $ R.tyPure $ R.F $ TyBuiltin (PIRTypeList Nothing)
          ] (R.tyPure $ R.B a 0)
tlaTyBuiltin P.TailList             =
  let a = R.Ann (fromString "a") in
  TlaAll a R.KStar $
    -- We want lists of a,
    -- but since the 'PIRType' does not include variable,
    -- 'Nothing' is used to represent it.
    TlaOp [ TlaVal $ R.tyPure $ R.F $ TyBuiltin (PIRTypeList Nothing)
          ] (R.tyPure $ R.F $ TyBuiltin (PIRTypeList Nothing))
tlaTyBuiltin P.UnBData              = TlaOp [tlaTyData] pirTyBS
tlaTyBuiltin P.UnIData              = TlaOp [tlaTyData] pirTyNat
tlaTyBuiltin P.BData                = TlaOp [tlaTyBS] pirTyData
tlaTyBuiltin b = error ("Unsuported builtin: " ++ show b)


tlaTyConstant :: PIRConstant -> TlaType
tlaTyConstant y = tlaTyNat


instance Pretty TlaType where
  prettyPrec d t@TlaAll{} = parensIf (d > 10) $ assoclBinder (pretty "∀") isAll d t
    where isAll (TlaAll ann tx body) = Just (ann, tx, body)
          isAll _                    = Nothing
  prettyPrec d (TlaVal  t)       = pretty t
  prettyPrec d (TlaOp   tys res) =
    pretty "Op" <> parens (sep $ punctuate comma $ map pretty tys)
      <+> pretty "->" <+> pretty res
  prettyPrec d (TlaSet  t)       =
    parensIf (d > 10) $ pretty "SetOf" <+> prettyPrec 11 t
  prettyPrec d (TlaTyOp tys res) =
    pretty "TyOp" <> parens (sep $ punctuate comma $ map pretty tys)
      <+> pretty "->" <+> pretty (TlaSet res)
