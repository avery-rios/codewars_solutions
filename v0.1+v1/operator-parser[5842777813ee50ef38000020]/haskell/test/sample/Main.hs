module Main (main) where

import Test.Hspec
import OperatorParserSpec (spec)

main :: IO ()
main = hspec spec