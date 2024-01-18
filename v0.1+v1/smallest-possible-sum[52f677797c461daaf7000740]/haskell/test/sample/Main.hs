module Main (main) where

import Test.Hspec
import Test.SmallestPossibleSumSpec (spec)

main :: IO ()
main = hspec spec