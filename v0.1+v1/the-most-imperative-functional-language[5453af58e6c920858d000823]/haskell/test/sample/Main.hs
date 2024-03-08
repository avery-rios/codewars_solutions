module Main (main) where

import Test.Hspec
import ImperativeSpec (spec)

main :: IO ()
main = hspec spec