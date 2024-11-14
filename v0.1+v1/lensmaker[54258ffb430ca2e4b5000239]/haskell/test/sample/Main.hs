module Main (main) where

import Test.Hspec
import MicroLensSpec (spec)
             
main :: IO ()
main = hspec spec
