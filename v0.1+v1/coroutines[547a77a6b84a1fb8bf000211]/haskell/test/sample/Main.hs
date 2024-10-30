module Main (main) where

import Test.Hspec
import CoroutineSpec (spec)
             
main :: IO ()
main = hspec spec
