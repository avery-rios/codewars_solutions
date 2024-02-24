module Main (main) where

import Test.Hspec
import ApplicativeParserSpec (spec)

main :: IO ()
main = hspec spec