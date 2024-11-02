module Main (main) where

import Test.Hspec
import PolyvariadicFunctionsSpec (spec)
             
main :: IO ()
main = hspec spec
