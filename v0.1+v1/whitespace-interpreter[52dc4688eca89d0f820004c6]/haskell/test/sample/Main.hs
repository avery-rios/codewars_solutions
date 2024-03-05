module Main (main) where

import Test.Hspec
import ExampleSpec (spec)

main :: IO ()
main = hspec spec