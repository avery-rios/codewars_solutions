module Main (main) where

import Test.Hspec
import AlphabeticAnagramsSpec (spec)

main :: IO ()
main = hspec spec