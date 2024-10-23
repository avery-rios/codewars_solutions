module Main (main) where

import Test.Hspec
import CombinatorsSpec (spec)
             
main :: IO ()
main = hspec spec
