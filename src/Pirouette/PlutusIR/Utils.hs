{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
module Pirouette.PlutusIR.Utils where

import           Pirouette.Monad
import           Pirouette.Monad.Maybe
import qualified Pirouette.Term.Syntax.SystemF as R
import           Pirouette.Term.Syntax
import           Pirouette.PlutusIR.ToTerm

import qualified PlutusCore         as P

import           Control.Monad.Trans
import           Data.Data
import qualified Data.Text as T

-- Auxiliar instance declarations
deriving instance Data P.Unique
deriving instance Data P.Name
deriving instance Data P.TyName


-- TODO: actually check that the given name is a constructor of
-- a declared 'Bool' datatype.
termIsBoolVal :: (PirouetteReadDefs PlutusIR m) => Bool -> PirTerm -> m Bool
termIsBoolVal b (R.Free (FreeName n)) = consIsBoolVal b n
termIsBoolVal _ _                     = return False

consIsBoolVal :: (PirouetteReadDefs PlutusIR m) => Bool -> Name -> m Bool
consIsBoolVal b n = return $ nameString n == T.pack (show b)

consIsMaybeVal :: (PirouetteReadDefs PlutusIR m) => Name -> MaybeT m (Maybe ())
consIsMaybeVal n
  | nameString n == "Just"    = return (Just ())
  | nameString n == "Nothing" = return Nothing
  | otherwise                 = fail "Not a constructor from Maybe"

-- TODO: Similarly to 'termIsBoolVal', check this is really a unit type
typeIsUnit :: (PirouetteReadDefs PlutusIR m) => PirType -> m Bool
typeIsUnit (R.TyApp (R.F (TyFree n)) []) = return $ nameString n == "Unit"
typeIsUnit _                             = return False

tynameIsBool :: (PirouetteReadDefs PlutusIR m) => Name -> m Bool
tynameIsBool n = return $ nameString n == "Bool"

typeIsBool :: (PirouetteReadDefs PlutusIR m) => PirType -> m Bool
typeIsBool (R.TyApp (R.F (TyFree n)) []) = tynameIsBool n
typeIsBool _ = return False


nameIsITE :: TermBase PlutusIR name -> Bool
nameIsITE (Builtin P.IfThenElse) = True
nameIsITE _ = False


{-

consIsUnit :: DisambFN P.TyName P.Name -> Bool
consIsUnit (ConsOf n 0 ty) = P.nameString n == "Unit" && P.nameString (P.unTyName ty) == "Unit"
consIsUnit _               = False

consIsJust :: DisambFN P.TyName P.Name -> Bool
consIsJust (ConsOf n _ ty) = P.nameString n == "Just" && P.nameString (P.unTyName ty) == "Maybe"
consIsJust _               = False

consIsNothing :: DisambFN P.TyName P.Name -> Bool
consIsNothing (ConsOf n _ ty) = P.nameString n == "Nothing" && P.nameString (P.unTyName ty) == "Maybe"
consIsNothing _               = False

consIsTrue :: DisambFN P.TyName P.Name -> Bool
consIsTrue (ConsOf n 0 ty) = P.nameString n == "True" && P.nameString (P.unTyName ty) == "Bool"
consIsTrue _               = False

consIsFalse :: DisambFN P.TyName P.Name -> Bool
consIsFalse (ConsOf n 1 ty) = P.nameString n == "False" && P.nameString (P.unTyName ty) == "Bool"
consIsFalse _               = False

-- ** Term Predicates from PlutusIR

class TyHasUnit tyname where
  tynameIsUnit :: tyname -> Bool

  typeIsUnit :: Type tyname -> Bool
  typeIsUnit (Raw.TyApp (Raw.F (TyFree n)) []) = tynameIsUnit n
  typeIsUnit _ = False

class TyHasMaybe tyname where
  tynameIsMaybe :: tyname -> Bool

class TyHasTuples tyname where
  tynameIsTuple :: tyname -> Bool

class TyHasBooleans tyname where
  tynameIsBool :: tyname -> Bool

class TermHasBooleans name where
  nameIsBool :: Bool -> name -> Bool

class TermHasMaybe name where
  nameIsJust    :: name -> Bool
  nameIsNothing :: name -> Bool

  termIsJust :: (TyHasMaybe tyname) => Term tyname name rest -> Bool
  termIsJust (Raw.App (Raw.F (FreeName (ConsOf n _ ty))) _) = tynameIsMaybe ty && nameIsJust n
  termIsJust _ = False

  termIsNothing :: (TyHasMaybe tyname) => Term tyname name rest -> Bool
  termIsNothing (Raw.App (Raw.F (FreeName (ConsOf n _ ty))) _) = tynameIsMaybe ty && nameIsNothing n
  termIsNothing _ = False

type HasBooleans tyname name = (ToText tyname, ToText name, TyHasBooleans tyname, TermHasBooleans name)
type HasMaybe    tyname name = (ToText tyname, ToText name, TyHasMaybe tyname, TermHasMaybe name)

class ToText n where
  toText :: n -> T.Text

instance ToText Name where
  toText = nameString
instance ToText P.Name where
  toText = P.nameString
instance ToText P.TyName where
  toText = toText . P.unTyName

instance (ToText ty) => TyHasUnit ty where
  tynameIsUnit n = toText n == "Unit"

instance (ToText ty) => TyHasBooleans ty where
  tynameIsBool n = toText n == "Bool"

instance (ToText ty) => TyHasTuples ty where
  tynameIsTuple n = toText n == "Tuple2"

instance (ToText ty) => TyHasMaybe ty where
  tynameIsMaybe n = toText n == "Maybe"

instance ToText n => TermHasBooleans n where
  nameIsBool t n = toText n == T.pack (show t)

instance ToText n => TermHasMaybe n where
  nameIsJust    n = toText n == "Just"
  nameIsNothing n = toText n == "Nothing"

termIsBool :: (HasBooleans tyname name) => Bool -> Term tyname name rest -> Bool
termIsBool t (Raw.Free (FreeName (ConsOf n _ ty))) = nameIsBool t n && tynameIsBool ty
termIsBool _ _ = False

termIsUnit :: Term P.TyName P.Name fun -> Bool
termIsUnit (Raw.Free (FreeName c)) = consIsUnit c
termIsUnit _                       = False

-}
