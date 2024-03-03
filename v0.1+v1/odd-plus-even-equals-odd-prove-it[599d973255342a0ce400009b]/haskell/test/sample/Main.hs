module Main (main) where

import Test.Hspec
import OddsAndEvensSpec (spec)

main :: IO ()
main = hspec spec