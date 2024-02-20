module Main (main) where

import Test.Hspec
import EvaluateMathematicalExpressionSpec (spec)

main :: IO ()
main = hspec spec