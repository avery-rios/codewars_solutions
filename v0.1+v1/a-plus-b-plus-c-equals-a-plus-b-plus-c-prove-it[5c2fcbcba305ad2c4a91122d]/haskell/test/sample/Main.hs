module Main (main) where

import Test.Hspec
import Kata.AdditionAssoc.TestSpec (spec)
             
main :: IO ()
main = hspec spec
