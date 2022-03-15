import Test.Tasty

import qualified Pirouette.Term.TransformationsSpec as Tr
import qualified Pirouette.Term.Syntax.SystemFSpec as SF
import qualified Pirouette.PlutusIR.ToTermSpec as FP

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup ""
  [ SF.tests ]
  -- describe "SystemF"          SF.spec
  -- describe "Transformations"  Tr.spec
  -- describe "FromPlutusIR"     FP.spec
