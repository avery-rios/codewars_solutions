module Main (main) where

import Test.Hspec
import LispLovesMeSpec (spec)

main :: IO ()
main = hspec spec