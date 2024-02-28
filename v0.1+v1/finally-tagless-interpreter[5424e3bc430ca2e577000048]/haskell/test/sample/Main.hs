module Main (main) where

import Test.Hspec
import TaglessSpec (spec)

main :: IO ()
main = hspec spec