module Test.SmallestPossibleSumSpec where

import Kata.SmallestPossibleSum (smallestPossibleSum)
import Test.Hspec

spec = do
  describe "smallest possible sum" $ do
    it "example tests" $ do
      smallestPossibleSum [6,9,21] `shouldBe` 9
      smallestPossibleSum [1,21,55] `shouldBe` 3
      smallestPossibleSum [3,13,23,7,83] `shouldBe` 5
      smallestPossibleSum [4,16,24] `shouldBe` 12
      smallestPossibleSum [30,12] `shouldBe` 12
      smallestPossibleSum [60,12,96,48,60,24,72,36,72,72,48] `shouldBe` 132
      smallestPossibleSum [71,71,71,71,71,71,71,71,71,71,71,71,71] `shouldBe` 923
      smallestPossibleSum [11,22] `shouldBe` 22
      smallestPossibleSum [9] `shouldBe` 9