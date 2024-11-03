module Main (main) where

import Test.Hspec
import FabergeSpec (spec)
             
main :: IO ()
main = hspec spec
