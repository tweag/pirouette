import qualified Language.Pirouette.PlutusIR.ToTermSpec as FP
import qualified Pirouette.Term.Syntax.SystemFSpec as SF
import qualified Pirouette.Term.TransformationsSpec as Tr
import Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Pirouette"
    [ testGroup "SystemF" SF.tests,
      testGroup "PlutusIR" FP.tests,
      testGroup "Term" [ testGroup "Transformations" Tr.tests ]
    ]
