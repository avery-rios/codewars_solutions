{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Become.Immortal
import Test.Hspec

fixedTest :: (Integer, Integer, Integer, Integer) -> Integer -> Spec
fixedTest tst@(m, n, l, t) r =
  it (show tst) (elderAge m n l t `shouldBe` r)

main :: IO ()
main = hspec do
  fixedTest (347, 973, 1, 375) 47
