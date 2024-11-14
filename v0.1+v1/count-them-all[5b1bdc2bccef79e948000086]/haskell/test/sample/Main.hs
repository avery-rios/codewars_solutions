module Main (main) where

import Test.Hspec
import CountingSpec (spec)
             
main :: IO ()
main = hspec spec
