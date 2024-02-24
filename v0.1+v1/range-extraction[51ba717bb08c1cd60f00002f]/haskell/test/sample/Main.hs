module Main (main) where

import Test.Hspec
import RangeExtractor.JorgeVS.KataSpec (spec)

main :: IO ()
main = hspec spec