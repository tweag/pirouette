import Test.Hspec

import qualified Pirouette.Term.TransformationsSpec as Tr

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "Transformations"  Tr.spec
