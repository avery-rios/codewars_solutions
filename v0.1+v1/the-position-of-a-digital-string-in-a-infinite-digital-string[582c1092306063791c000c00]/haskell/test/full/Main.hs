module Main (main) where

import InfiniteDigitalStringSpec (spec)
import Test.Hspec

main :: IO ()
main = hspec spec