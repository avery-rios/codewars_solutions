module Main (main) where

import Test.Hspec
import SymbolicDifferentiationOfPrefixExpressionsSpec (spec)

main :: IO ()
main = hspec spec