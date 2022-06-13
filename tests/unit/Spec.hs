import qualified Language.Pirouette.ExampleSpec as Ex
import qualified Language.Pirouette.PlutusIR.ToTermSpec as FP
import qualified Language.Pirouette.PlutusIR.BuiltinsSpec as PIRBuiltins
import qualified Pirouette.Term.Syntax.SystemFSpec as SF
import qualified Pirouette.Term.SymbolicEvalSpec as SymbolicEval
import qualified Pirouette.Term.SymbolicProveSpec as SymbolicProve
import qualified Pirouette.Term.TransformationsSpec as Tr
import qualified Pirouette.Transformations.DefunctionalizationSpec as Defunc
import qualified Pirouette.Transformations.EtaExpandSpec as Eta
import qualified Pirouette.Transformations.MonomorphizationSpec as Mono
import qualified Pirouette.Transformations.PrenexSpec as Prenex
import qualified Pirouette.Term.Syntax.BaseSpec as Base
import Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Pirouette"
    [ testGroup "SystemF" SF.tests,
      testGroup
        "Transformations"
        [testGroup "Defunctionalization" Defunc.tests,
         testGroup "EtaExpand" Eta.tests,
         testGroup "Monomorphization" Mono.tests,
         testGroup "Prenex" Prenex.tests],
      testGroup
        "Term" 
        [testGroup "Base" Base.tests,
         testGroup "Transformations" Tr.tests,
         testGroup "Symbolic evaluation" SymbolicEval.tests,
         testGroup "Symbolic prove" SymbolicProve.tests],
      testGroup
        "Language"
        [ testGroup "PlutusIR"
          [ testGroup "ToTerm" FP.tests,
            testGroup "Builtins" PIRBuiltins.tests
          ],
          testGroup "Example" Ex.tests
        ]
    ]
