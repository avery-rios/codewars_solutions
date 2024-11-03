module Main (main) where

import Test.Hspec
import ListsAsFoldsIISpec (spec)
             
main :: IO ()
main = hspec spec
