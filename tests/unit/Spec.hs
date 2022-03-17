import qualified Language.Pirouette.PlutusIR.ToTermSpec as FP
import qualified Language.Pirouette.ExampleSpec as Ex
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
      testGroup "Term" [ testGroup "Transformations" Tr.tests ],
      testGroup "Language" [
        testGroup "PlutusIR" FP.tests,
        testGroup "Example" Ex.tests
      ]
    ]
