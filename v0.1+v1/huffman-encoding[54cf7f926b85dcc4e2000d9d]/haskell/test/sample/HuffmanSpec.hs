module HuffmanSpec where

import Test.Hspec
import Huffman

spec :: Spec
spec = do
    describe "basic tests" $ let fs = frequencies "aaaabcc" in do
        it "aaaabcc encoded should have length 10" $
            fmap length (encode fs "aaaabcc") `shouldBe` Just 10
        it "empty list encode" $
            encode fs [] `shouldBe` Just []
        it "empty list decode" $
            decode fs [] `shouldBe` Just []
    
    describe "length" $ do
        it "equal lengths with same frequencies if alphabet size is a power of two" $
            let enc = encode [('a', 1), ('b', 1)]
            in mapM (fmap length) [enc "a", enc "b"] `shouldBe` Just [1, 1]
        it "smaller length for higher frequency, if size of alphabet is not power of two" $
            let enc = encode [('a', 1), ('b', 1), ('c', 2)]
            in mapM (fmap length) [enc "a", enc "b", enc "c"] `shouldBe` Just [2, 2, 1]

    describe "error handling" $ do
        it "empty frequencies encode 1" $ encode [] "abc" `shouldBe` Nothing
        it "empty frequencies encode 2" $ encode [] "" `shouldBe` Nothing
        it "singleton frequency encode 1" $ encode [('a', 1)] "a" `shouldBe` Nothing
        it "singleton frequency encode 2" $ encode [('a', 1)] "" `shouldBe` Nothing
        
        it "empty frequencies decode 1" $ (decode [] [Z, O] :: Maybe String) `shouldBe` Nothing
        it "empty frequencies decode 2" $ (decode [] [] :: Maybe String) `shouldBe` Nothing
        it "singleton frequency decode 1" $ decode [('a', 1)] [Z, O] `shouldBe` Nothing
        it "singleton frequency decode 2" $ decode [('a', 1)] [] `shouldBe` Nothing