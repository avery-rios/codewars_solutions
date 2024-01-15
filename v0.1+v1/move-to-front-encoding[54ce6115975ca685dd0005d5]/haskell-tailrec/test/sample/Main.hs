module Main (main) where

import Test.Hspec
import MTFSpec (spec)

main :: IO ()
main = hspec spec