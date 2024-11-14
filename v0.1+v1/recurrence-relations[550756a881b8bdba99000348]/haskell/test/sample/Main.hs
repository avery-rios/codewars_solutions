module Main (main) where

import Test.Hspec
import FunctionEvaluatorSpec (spec)
             
main :: IO ()
main = hspec spec
