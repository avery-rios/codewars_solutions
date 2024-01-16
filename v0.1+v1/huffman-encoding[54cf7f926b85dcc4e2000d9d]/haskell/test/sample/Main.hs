module Main (main) where

import Test.Hspec
import HuffmanSpec (spec)

main :: IO ()
main = hspec spec