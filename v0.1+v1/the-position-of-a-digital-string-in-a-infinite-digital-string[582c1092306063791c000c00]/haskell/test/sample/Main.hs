module Main (main) where

import Test.Hspec
import InfiniteDigitalStringSpec (spec)
             
main :: IO ()
main = hspec spec
