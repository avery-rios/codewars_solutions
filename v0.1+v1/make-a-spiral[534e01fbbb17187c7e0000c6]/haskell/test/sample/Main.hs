module Main (main) where

import Test.Hspec
import SpiralSpec (spec)

main :: IO ()
main = hspec spec