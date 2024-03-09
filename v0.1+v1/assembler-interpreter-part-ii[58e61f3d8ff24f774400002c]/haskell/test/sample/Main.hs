module Main (main) where

import Test.Hspec
import AssemblerInterpreterSpec (spec)

main :: IO ()
main = hspec spec