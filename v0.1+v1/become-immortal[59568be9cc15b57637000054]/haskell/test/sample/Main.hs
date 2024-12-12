module Main (main) where

import Test.Hspec
import Become.ImmortalSpec (spec)
             
main :: IO ()
main = hspec spec
