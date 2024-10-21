module Main (main) where

import Test.Hspec
import ScottEncodingSpec (spec)

main :: IO ()
main = hspec spec