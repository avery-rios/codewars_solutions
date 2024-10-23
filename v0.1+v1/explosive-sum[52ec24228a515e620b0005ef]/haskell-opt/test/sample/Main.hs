module Main (main) where

import Test.Hspec
import ExplosiveSumSpec (spec)
             
main :: IO ()
main = hspec spec
