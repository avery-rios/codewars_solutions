module SymbolicDifferentiationOfPrefixExpressionsSpec where

import Control.Monad (when)
import SymbolicDifferentiationOfPrefixExpressions (diff)
import Test.Hspec

spec :: Spec
spec = do
  it "simple expressions" $ do
    diff "5" `shouldBe` "0"
    diff "x" `shouldBe` "1"
    diff "(+ x x)" `shouldBe` "2"
    diff "(- x x)" `shouldBe` "0"
    diff "(* x 2)" `shouldBe` "2"
    diff "(/ x 2)" `shouldBe` "0.5"
    diff "(^ x 2)" `shouldBe` "(* 2 x)"
    diff "(cos x)" `shouldBe` "(* -1 (sin x))"
    diff "(sin x)" `shouldBe` "(cos x)"
    diff "(tan x)" `shouldBe` "(+ 1 (^ (tan x) 2))"
    diff "(exp x)" `shouldBe` "(exp x)"
    diff "(ln x)" `shouldBe` "(/ 1 x)"
  it "Nested expressions" $ do
    diff "(+ x (+ x x))" `shouldBe` "3"
    diff "(- (+ x x) x)" `shouldBe` "1"
    diff "(* 2 (+ x 2))" `shouldBe` "2"
    diff "(/ 2 (+ 1 x))" `shouldBe` "(/ -2 (^ (+ 1 x) 2))"
    diff "(cos (+ x 1))" `shouldBe` "(* -1 (sin (+ x 1)))"

    -- Accepting (* 2 (* -1 (sin (* 2 x)))) or (* -2 (sin (* 2 x)))
    let result = diff "(cos (* 2 x))"
    when (result /= "(* 2 (* -1 (sin (* 2 x))))" && result /= "(* -2 (sin (* 2 x)))") $
      expectationFailure $
        "`diff \"(cos (* 2 x))\"`: expected either \"(* 2 (* -1 (sin (* 2 x))))\" or \"(* -2 (sin (* 2 x)))\", but got \"" ++ result ++ "\""

    diff "(sin (+ x 1))" `shouldBe` "(cos (+ x 1))"
    diff "(sin (* 2 x))" `shouldBe` "(* 2 (cos (* 2 x)))"
    diff "(tan (* 2 x))" `shouldBe` "(* 2 (+ 1 (^ (tan (* 2 x)) 2)))"
    diff "(exp (* 2 x))" `shouldBe` "(* 2 (exp (* 2 x)))"

  it "Second derivatives" $ do
    diff (diff "(sin x)") `shouldBe` "(* -1 (sin x))"
    diff (diff "(exp x)") `shouldBe` "(exp x)"

    -- Accepting (* 3 (* 2 x)) or (* 6 x)
    let result = diff (diff "(^ x 3)")
    when (result /= "(* 3 (* 2 x))" && result /= "(* 6 x)") $
      expectationFailure $
        "`diff (diff \"(^ x 3)\")`: expected either \"(* 3 (* 2 x))\" or \"(* 6 x)\", but got \"" ++ result ++ "\""
