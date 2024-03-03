module Main (main) where

import Test.Hspec
import Kata.AdditionCommutesSpec (spec)

main :: IO ()
main = hspec spec