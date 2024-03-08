module Main (main) where

import Test.Hspec
import PCSpec (spec)

main :: IO ()
main = hspec spec