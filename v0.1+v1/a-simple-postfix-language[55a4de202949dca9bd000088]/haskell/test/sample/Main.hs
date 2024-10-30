module Main (main) where

import Test.Hspec
import PostfixSpec (spec)
             
main :: IO ()
main = hspec spec
