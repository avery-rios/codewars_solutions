module Main (main) where

import Test.Hspec
import YonedaLemmaExampleSpec (spec)
             
main :: IO ()
main = hspec spec
