{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module declares 'PlutusIR' as a supported language, instantiates all the
--  necessary bits for using the facilities from "Pirouette.Term.Syntax" and provides
--  a translation function 'trProgram' to translate a plutusIR program into a 'PrtTerm'
--  and a map of definitions.
module Language.Pirouette.PlutusIR.Syntax where

import Control.Monad.Combinators.Expr
import qualified Data.ByteString as BS
import Data.Data
import Data.Foldable
import Data.Maybe (isJust)
import qualified Data.Set as S
import qualified Data.Text as T
import Language.Haskell.TH.Syntax (Lift)
import Language.Pirouette.QuasiQuoter.Syntax hiding (TyAll, TyApp, TyFun)
import Pirouette.Term.Syntax
import Pirouette.Term.Syntax.SystemF as SystF
import PlutusCore
  ( DefaultUni (..),
    pattern DefaultUniList,
    pattern DefaultUniPair,
    pattern DefaultUniString,
  )
import qualified PlutusCore as P
import qualified PlutusCore.Data as P
import Prettyprinter hiding (Pretty, pretty)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- * Declaring the builtins of PlutusIR.

-- | Defining the 'PlutusIR' as a language, which contains a set of builtin (types and terms)
-- and constants.
data PlutusIR
  deriving (Data, Typeable)

deriving instance Data P.DefaultFun

deriving instance Lift P.DefaultFun

deriving instance Lift P.Data

type PIRDefaultFun = P.DefaultFun

instance LanguageBuiltins PlutusIR where
  type BuiltinTypes PlutusIR = PIRBuiltinType
  type BuiltinTerms PlutusIR = PIRDefaultFun
  type Constants PlutusIR = PIRConstant

  builtinTypeDefinitions definedTypes =
    -- only define List and Unit if they are not yet defined
    [("List", listTypeDef) | not (isDefined "List")]
      ++ [("Unit", unitTypeDef) | not (isDefined "Unit")]
      ++ [("Tuple2", tuple2TypeDef) | not (isDefined "Tuple2")]
      ++ [("Data", dataTypeDef)]
    where
      a = TyApp (Bound (Ann "a") 0) []
      b = TyApp (Bound (Ann "a") 1) []

      isDefined nm = isJust (lookup nm definedTypes)

      listOf x = TyApp (Free $ TySig "List") [x]
      tuple2Of x y = TyApp (Free $ TySig "Tuple2") [x, y]
      builtin nm = TyApp (Free $ TyBuiltin nm) []

      listTypeDef =
        Datatype
          { kind = KTo KStar KStar,
            typeVariables = [("a", KStar)],
            destructor = "Nil_match",
            constructors =
              [ ("Nil", TyAll (Ann "a") KStar (listOf a)),
                ("Cons", TyAll (Ann "a") KStar (TyFun a (TyFun (listOf a) (listOf a))))
              ]
          }

      unitTypeDef =
        Datatype
          { kind = KStar,
            typeVariables = [],
            destructor = "Unit_match",
            constructors = [("Unit", builtin PIRTypeUnit)]
          }

      -- !! warning, we define it as "Tuple2 b a" to reuse 'a' for both list and tuple
      tuple2TypeDef =
        Datatype
          { kind = KTo KStar (KTo KStar KStar),
            typeVariables = [("b", KStar), ("a", KStar)],
            destructor = "Tuple2_match",
            constructors =
              [ ("Tuple2", TyAll (Ann "b") KStar $ TyAll (Ann "a") KStar $ TyFun b (TyFun a (tuple2Of b a)))
              ]
          }

      -- defined following https://github.com/input-output-hk/plutus/blob/master/plutus-core/plutus-core/src/PlutusCore/Data.hs
      dataTypeDef =
        Datatype
          { kind = KStar,
            typeVariables = [],
            destructor = "Data_match",
            constructors =
              [ ("Data_Constr", TyFun (builtin PIRTypeInteger) (TyFun tyListData tyData)),
                ("Data_Map", TyFun (builtin $ PIRTypeList (Just (PIRTypePair (Just PIRTypeData) (Just PIRTypeData)))) tyData),
                ("Data_List", TyFun tyListData tyData),
                ("Data_I", TyFun (builtin PIRTypeInteger) tyData),
                ("Data_B", TyFun (builtin PIRTypeByteString) tyData)
              ]
          }

      tyListData = builtin (PIRTypeList (Just PIRTypeData))
      tyData = builtin PIRTypeData

cstToBuiltinType :: PIRConstant -> PIRBuiltinType
cstToBuiltinType (PIRConstInteger _) = PIRTypeInteger
cstToBuiltinType (PIRConstByteString _) = PIRTypeByteString
cstToBuiltinType PIRConstUnit = PIRTypeUnit
cstToBuiltinType (PIRConstBool _) = PIRTypeBool
cstToBuiltinType (PIRConstString _) = PIRTypeString
cstToBuiltinType (PIRConstList []) = PIRTypeList Nothing
cstToBuiltinType (PIRConstList (c : cs)) =
  let res = PIRTypeList (Just $ cstToBuiltinType c)
   in if all (== res) (cstToBuiltinType <$> cs)
        then res
        else error "typeOfConstant: mismatching element types in a PIRConstList"
cstToBuiltinType (PIRConstPair c1 c2) =
  PIRTypePair (Just (cstToBuiltinType c1)) (Just (cstToBuiltinType c2))
cstToBuiltinType (PIRConstData _) = PIRTypeData

-- | Builtin Plutus Types
data PIRBuiltinType
  = PIRTypeInteger
  | PIRTypeByteString
  | PIRTypeUnit
  | PIRTypeBool
  | PIRTypeString
  | PIRTypeData
  | PIRTypeList (Maybe PIRBuiltinType)
  | PIRTypePair (Maybe PIRBuiltinType) (Maybe PIRBuiltinType)
  deriving (Eq, Ord, Show, Read, Data, Typeable, Lift)

defUniToType :: forall k (a :: k). DefaultUni (P.Esc a) -> PIRBuiltinType
defUniToType DefaultUniInteger = PIRTypeInteger
defUniToType DefaultUniByteString = PIRTypeByteString
defUniToType DefaultUniUnit = PIRTypeUnit
defUniToType DefaultUniBool = PIRTypeBool
defUniToType DefaultUniString = PIRTypeString
defUniToType DefaultUniData = PIRTypeData
defUniToType (DefaultUniList a) = PIRTypeList (Just (defUniToType a))
defUniToType (DefaultUniPair a b) = PIRTypePair (Just $ defUniToType a) (Just $ defUniToType b)
defUniToType DefaultUniProtoList = PIRTypeList Nothing
defUniToType DefaultUniProtoPair = PIRTypePair Nothing Nothing
defUniToType (DefaultUniApply DefaultUniProtoPair a) = PIRTypePair (Just $ defUniToType a) Nothing
defUniToType x = error $ "defUniToType impossible: " ++ show x

-- | Untyped Plutus Constants
data PIRConstant
  = PIRConstInteger Integer
  | PIRConstByteString BS.ByteString
  | PIRConstUnit
  | PIRConstBool Bool
  | PIRConstString T.Text
  | PIRConstList [PIRConstant]
  | PIRConstPair PIRConstant PIRConstant
  | PIRConstData P.Data
  deriving (Eq, Ord, Show, Data, Typeable, Lift)

defUniToConstant :: DefaultUni (P.Esc a) -> a -> PIRConstant
defUniToConstant DefaultUniInteger x = PIRConstInteger x
defUniToConstant DefaultUniByteString x = PIRConstByteString x
defUniToConstant DefaultUniUnit _ = PIRConstUnit
defUniToConstant DefaultUniBool x = PIRConstBool x
defUniToConstant DefaultUniString x = PIRConstString x
defUniToConstant DefaultUniData x = PIRConstData x
defUniToConstant (DefaultUniList a) x = PIRConstList (map (defUniToConstant a) x)
defUniToConstant (DefaultUniPair a b) x = PIRConstPair (defUniToConstant a (fst x)) (defUniToConstant b (snd x))
defUniToConstant uni _ = error $ "defUniToConstant impossible: " ++ show uni

instance Pretty PIRBuiltinType where
  pretty PIRTypeInteger = "Integer"
  pretty PIRTypeByteString = "ByteString"
  pretty PIRTypeUnit = "Unit"
  pretty PIRTypeBool = "Bool"
  pretty PIRTypeString = "String"
  pretty PIRTypeData = "Data"
  pretty (PIRTypeList a) = brackets (sep ["List", pretty a])
  pretty (PIRTypePair a b) = brackets (sep ["Pair", pretty a, pretty b])

instance Pretty (Maybe PIRBuiltinType) where
  pretty Nothing = "-"
  pretty (Just t) = pretty t

instance Pretty PIRConstant where
  pretty (PIRConstInteger x) = pretty x
  pretty (PIRConstByteString x) = "b" <> pretty x
  pretty PIRConstUnit = "unit"
  pretty (PIRConstBool x) = pretty x
  pretty (PIRConstString x) = dquotes (pretty x)
  pretty (PIRConstData d) = "d" <> braces (pretty d)
  pretty (PIRConstList xs) = "l" <> brackets (sep $ punctuate comma $ map pretty xs)
  pretty (PIRConstPair x y) = "p" <> brackets (sep $ punctuate comma $ map pretty [x, y])

instance Pretty P.Data where
  pretty (P.Constr cN fields) = pretty cN <+> pretty fields
  pretty (P.Map kvs) = pretty kvs
  pretty (P.List xs) = pretty xs
  pretty (P.I i) = pretty i
  pretty (P.B bs) = pretty bs

-- * Parsing

instance LanguageParser PlutusIR where
  -- TODO: How about applied lists and pairs?
  parseBuiltinType =
    label "Builtin type" $
      asum $
        map
          try
          [ PIRTypeInteger <$ symbol "Integer",
            PIRTypeByteString <$ symbol "ByteString",
            PIRTypeUnit <$ symbol "Unit",
            PIRTypeBool <$ symbol "Bool",
            PIRTypeString <$ symbol "String",
            PIRTypeData <$ symbol "Data",
            PIRTypeList Nothing <$ symbol "List",
            PIRTypePair Nothing Nothing <$ symbol "Pair"
          ]

  -- TODO: more constants
  parseConstant =
    label "Constant" $
      asum $
        map
          try
          [ PIRConstInteger <$> try integer,
            PIRConstUnit <$ symbol "Unit",
            PIRConstBool <$> parseBoolean,
            PIRConstString . T.pack <$> stringLiteral
          ]
    where
      parseBoolean = (True <$ symbol "True") <|> (False <$ symbol "False")
      integer :: Parser Integer
      integer = L.lexeme spaceConsumer L.decimal
      -- copied from
      -- https://hackage.haskell.org/package/megaparsec/docs/Text-Megaparsec-Char-Lexer.html#v:charLiteral
      stringLiteral :: Parser String
      stringLiteral = L.lexeme spaceConsumer (char '"' >> manyTill L.charLiteral (char '"'))

  -- Taken from: https://github.com/input-output-hk/plutus/blob/3c81f60746f50b596d3209c38e048ebb473c93b8/plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs#L45
  parseBuiltinTerm =
    label "Builtin Term" $
      asum $
        map
          try
          [ -- Integers
            P.AddInteger <$ symbol "b/addInteger",
            P.SubtractInteger <$ symbol "b/subtractInteger",
            P.MultiplyInteger <$ symbol "b/multiplyInteger",
            P.DivideInteger <$ symbol "b/divideInteger",
            P.QuotientInteger <$ symbol "b/quotientInteger",
            P.RemainderInteger <$ symbol "b/remainderInteger",
            P.ModInteger <$ symbol "b/modInteger",
            P.EqualsInteger <$ symbol "b/equalsInteger",
            P.LessThanInteger <$ symbol "b/lessThanInteger",
            P.LessThanEqualsInteger <$ symbol "b/lessThanEqualsInteger",
            -- Bytestrings
            P.AppendByteString <$ symbol "b/appendByteString",
            P.ConsByteString <$ symbol "b/consByteString",
            P.SliceByteString <$ symbol "b/sliceByteString",
            P.LengthOfByteString <$ symbol "b/lengthOfByteString",
            P.IndexByteString <$ symbol "b/indexByteString",
            P.EqualsByteString <$ symbol "b/equalsByteString",
            P.LessThanByteString <$ symbol "b/lessThanByteString",
            P.LessThanEqualsByteString <$ symbol "b/lessThanEqualsByteString",
            -- Cryptography and hashes
            P.Sha2_256 <$ symbol "b/sha2",
            P.Sha3_256 <$ symbol "b/sha3",
            P.Blake2b_256 <$ symbol "b/blake2b",
            P.VerifySignature <$ symbol "b/verifySignature",
            -- P.VerifyEd25519Signature <$ symbol "b/verifyEd25519Signature",
            -- P.VerifyEcdsaSecp256k1Signature <$ symbol "b/verifyEcdsaSecp256k1Signature",
            -- P.VerifySchnorrSecp256k1Signature <$ symbol "b/verifySchnorrSecp256k1Signature",
            -- Strings
            P.AppendString <$ symbol "b/appendString",
            P.EqualsString <$ symbol "b/equalsString",
            P.EncodeUtf8 <$ symbol "b/encodeUtf8",
            P.DecodeUtf8 <$ symbol "b/decodeUtf8",
            -- Bool
            P.IfThenElse <$ symbol "b/ifThenElse",
            -- Unit
            P.ChooseUnit <$ symbol "b/chooseUnit",
            -- Tracing
            P.Trace <$ symbol "b/trace",
            -- Pairs
            P.FstPair <$ symbol "b/fstPair",
            P.SndPair <$ symbol "b/sndPair",
            -- Lists
            P.ChooseList <$ symbol "b/chooseList",
            P.MkCons <$ symbol "b/mkCons",
            P.HeadList <$ symbol "b/headList",
            P.TailList <$ symbol "b/tailList",
            P.NullList <$ symbol "b/nullList",
            -- Data
            -- It is convenient to have a "choosing" function for a data type that has more than two
            -- constructors to get pattern matching over it and we may end up having multiple such data
            -- types, hence we include the name of the data type as a suffix.
            P.ChooseData <$ symbol "b/chooseData",
            P.ConstrData <$ symbol "b/constrData",
            P.MapData <$ symbol "b/mapData",
            P.ListData <$ symbol "b/listData",
            P.IData <$ symbol "b/iData",
            P.BData <$ symbol "b/bData",
            P.UnConstrData <$ symbol "b/unConstrData",
            P.UnMapData <$ symbol "b/unMapData",
            P.UnListData <$ symbol "b/unListData",
            P.UnIData <$ symbol "b/unIData",
            P.UnBData <$ symbol "b/unBData",
            P.EqualsData <$ symbol "b/equalsData",
            -- Misc constructors
            P.MkPairData <$ symbol "b/mkPairData",
            P.MkNilData <$ symbol "b/mkNilData",
            P.MkNilPairData <$ symbol "b/mkNilPairData"
          ]

  -- Some builtins will also be available through more familiar infix operators
  operators =
    [ [ InfixR (symbol "*" >> return (exprBinApp P.MultiplyInteger)),
        InfixR (symbol "/" >> return (exprBinApp P.DivideInteger)),
        InfixR (symbol "%" >> return (exprBinApp P.ModInteger))
      ],
      [ InfixR (symbol "+" >> return (exprBinApp P.AddInteger)),
        InfixR (symbol "-" >> return (exprBinApp P.SubtractInteger))
      ],
      [ InfixN (symbol "<" >> return (exprBinApp P.LessThanInteger)),
        InfixN (symbol "<=" >> return (exprBinApp P.LessThanEqualsInteger)),
        InfixN (symbol "==i" >> return (exprBinApp P.EqualsInteger)),
        InfixN (symbol "==d" >> return (exprBinApp P.EqualsData)),
        InfixN (symbol "==bs" >> return (exprBinApp P.EqualsByteString)),
        InfixN (symbol "==s" >> return (exprBinApp P.EqualsString))
      ]
    ]

  reservedNames = S.fromList $ words "True False unit"
  reservedTypeNames = S.fromList $ words "Bool Unit List Data Pair String ByteString"

  ifThenElse resTy c t e = SystF.App (SystF.Free $ Builtin P.IfThenElse) $ SystF.TyArg resTy : map SystF.TermArg [c, t, e]
