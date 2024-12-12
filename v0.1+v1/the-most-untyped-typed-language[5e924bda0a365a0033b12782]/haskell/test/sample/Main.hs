module Main (main) where

import Test.Hspec
import UntypedSpec (spec)
             
main :: IO ()
main = hspec spec
