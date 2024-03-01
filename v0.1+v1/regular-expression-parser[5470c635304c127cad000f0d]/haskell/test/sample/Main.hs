module Main (main) where

import Test.Hspec
import RegExpParserSpec (spec)

main :: IO ()
main = hspec spec