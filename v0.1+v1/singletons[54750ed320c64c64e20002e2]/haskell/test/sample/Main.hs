module Main (main) where

import Test.Hspec
import SingletonsSpec (spec)

main :: IO ()
main = hspec spec