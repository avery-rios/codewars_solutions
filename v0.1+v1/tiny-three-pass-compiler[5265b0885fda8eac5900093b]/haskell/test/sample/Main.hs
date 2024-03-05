module Main (main) where

import Test.Hspec
import TinyThreePassCompilerSpec (spec)

main :: IO ()
main = hspec spec