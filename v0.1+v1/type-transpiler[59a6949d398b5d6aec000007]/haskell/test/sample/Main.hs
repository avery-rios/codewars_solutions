module Main (main) where

import Test.Hspec
import TypeTranspilerSpec (spec)
             
main :: IO ()
main = hspec spec
