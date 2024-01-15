module MTFSpec where

import MTF

import Test.Hspec

spec :: Spec
spec = do
    describe "basic examples for encode" $ do
        it "ababab" $ encode "abc" "ababab" `shouldBe` Just [0, 1, 1, 1, 1, 1]
        it "cccbbb" $ encode "abc" "cccbbb" `shouldBe` Just [2, 0, 0, 2, 0, 0]
        
    describe "basic examples for decode" $ do
        it "ababab" $ decode "abc" [0, 1, 1, 1, 1, 1] `shouldBe` Just "ababab"
        it "cccbbb" $ decode "abc" [2, 0, 0, 2, 0, 0] `shouldBe` Just "cccbbb"

    describe "error handling" $ do
        it "element not in alphabet" $ encode "abc" "x" `shouldBe` Nothing
        it "alphabet index out of bounds" $ decode "abc" [4] `shouldBe` Nothing
        it "negative indices" $ decode "abc" [(-1), (-2)] `shouldBe` Nothing