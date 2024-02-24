module Main (main) where

import Test.Hspec
import FibonacciSpec (spec)

main :: IO ()
main = hspec spec