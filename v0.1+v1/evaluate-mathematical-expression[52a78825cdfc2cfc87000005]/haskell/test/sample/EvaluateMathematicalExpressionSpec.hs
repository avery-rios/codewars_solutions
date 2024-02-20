module EvaluateMathematicalExpressionSpec (spec) where

import EvaluateMathematicalExpression (calc)
import Test.Hspec
import Data.Foldable (for_)

spec :: Spec
spec = do
  describe "example tests" $ do
    for_ [ ("1+1", 2)
         , ("1 - 1", 0)
         , ("1* 1", 1)
         , ("1 /1", 1)
         , ("-123", -123)
         , ("123", 123)
         , ("2 /2+3 * 4.75- -6", 21.25)
         , ("12* 123", 1476)
         , ("2 / (2 + 3) * 4.33 - -6", 7.732)
         ] $ \ ( arg, expected ) -> do
      it (show arg) $ do
        calc arg `shouldBe` expected