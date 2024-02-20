module Main (main) where

import Test.Hspec
import SnailSpec (spec)

main :: IO ()
main = hspec spec