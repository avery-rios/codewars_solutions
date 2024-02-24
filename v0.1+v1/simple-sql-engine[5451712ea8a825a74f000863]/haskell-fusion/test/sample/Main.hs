module Main (main) where

import Test.Hspec
import SimpleSQLEngineSpec (spec)

main :: IO ()
main = hspec spec