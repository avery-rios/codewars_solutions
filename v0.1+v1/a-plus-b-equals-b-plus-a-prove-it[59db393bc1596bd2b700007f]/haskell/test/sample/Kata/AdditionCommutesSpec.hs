module Kata.AdditionCommutesSpec where

import Kata.AdditionCommutes
import Test.Hspec

spec :: Spec
spec = do
  describe "My own tests" $ do
    it "My first test" $ do
      "Write your own tests here!" `shouldNotBe` "Good luck!"
