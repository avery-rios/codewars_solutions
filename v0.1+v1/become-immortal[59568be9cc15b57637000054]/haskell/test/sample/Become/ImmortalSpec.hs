module Become.ImmortalSpec where

import Become.Immortal (elderAge)
import Test.Hspec
import Test.QuickCheck

spec = do
  describe "Fixed tests" $ do
    it "You should pass these before meeting the Elder" $ do
      elderAge 8 5 1 100 `shouldBe` 5
      elderAge 8 8 0 1000007 `shouldBe` 224
      elderAge 25 31 0 1000007 `shouldBe` 11925
      elderAge 5 45 3 1000007 `shouldBe` 4323
      elderAge 31 39 7 2345 `shouldBe` 1586
      elderAge 545 435 342 1000007 `shouldBe` 808451
      elderAge 28827050410 35165045587 7109602 13719506 `shouldBe` 5456283