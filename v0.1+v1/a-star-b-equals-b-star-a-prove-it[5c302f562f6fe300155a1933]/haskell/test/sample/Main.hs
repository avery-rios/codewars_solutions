module Main (main) where

import Test.Hspec
import Kata.TimesComm.TestSpec (spec)
             
main :: IO ()
main = hspec spec
