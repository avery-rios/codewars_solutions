module Main (main) where

import Test.Hspec
import ISOSpec (spec)

main :: IO ()
main = hspec spec