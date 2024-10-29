module Main (main) where

import Test.Hspec
import PolynomFieldSpec (spec)
             
main :: IO ()
main = hspec spec
