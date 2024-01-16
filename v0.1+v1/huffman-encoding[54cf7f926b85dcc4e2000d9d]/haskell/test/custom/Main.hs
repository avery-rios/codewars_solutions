{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Huffman
import Test.Hspec

main :: IO ()
main = hspec do
  describe "encode should be inverse of decode" do
    let test name freq input =
          it name do
            (encode freq input >>= decode freq) `shouldBe` Just input
    test "t1" [('"', 1), ('~', 1)] "\"~"
    test "t2" [('V', 2), ('j', 1), ('\59577', 1)] "V\59577Vj"
  it "incomplete code should be rejected" do
    decode [('a', 1), ('b', 1), ('c', 2)] [Z] `shouldBe` Nothing
