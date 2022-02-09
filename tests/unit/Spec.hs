import Test.Hspec

import qualified Pirouette.Term.TransformationsSpec as Tr
import qualified Pirouette.Term.Syntax.SystemFSpec as SF
import qualified Pirouette.PlutusIR.ToTermSpec as FP


main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "SystemF"          SF.spec
  describe "Transformations"  Tr.spec
  describe "FromPlutusIR"     FP.spec
