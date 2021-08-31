
module Pirouette.Specializer.TypeDecl where

import           Pirouette.Term.Syntax

import qualified Language.TLAPlus.Syntax as TLA

data TypeSpecializer = TypeSpecializer {
  spzSet :: TLA.AS_UnitDef,
  spzConstructors :: [TLA.AS_UnitDef],
  spzDestructor :: TLA.AS_UnitDef,
  -- `spzMatch x c [a1,a2,a3] fn exp` outputs a translation of `match x with c(a1,a2,a3) -> exp`,
  -- using `fn` as a free name to represent `x` if required.
  spzMatch :: TLA.AS_Expression -> Name -> [Name] -> TLA.AS_Expression -> TLA.AS_Expression -> TLA.AS_Expression
}

