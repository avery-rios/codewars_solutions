module Main (main) where

import Test.Hspec
import TranspilerSpec (spec)
             
main :: IO ()
main = hspec spec
