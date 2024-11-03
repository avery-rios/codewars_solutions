{-# OPTIONS_GHC -O3 -optc-O3 #-}

module FabergeSpec (spec) where

import Faberge hiding (mo)
import GHC.Integer.GMP.Internals (powModInteger)
import Test.Hspec
import Test.QuickCheck

mo = 998244353

sumModBin' :: Integer -> Integer -> Integer
sumModBin' n k = fst $ foldl go (0, (1, 1)) [0 .. k - 1]
  where
    go (s, (nm, dm)) i =
      let nn = (nm * (n - i)) `rem` mo
          nd = (dm * (i + 1)) `rem` mo
          ss = (s + nn * powModInteger nd (mo - 2) mo) `rem` mo
       in (ss, (nn, nd))

height' :: Integer -> Integer -> Integer
height' n m
  | n > m = (powModInteger 2 m mo - 1) `rem` mo
  | n > m `div` 2 = ((mo - 2) + powModInteger 2 m mo - height' (m - n - 1) m) `rem` mo
  | otherwise = sumModBin' (m `rem` mo) n

tst n m = height n m `shouldBe` height' n m

spec :: Spec
spec = do
  describe "Faberge" $ do
    it "should work for some basic tests" $ do
      height 1 51 `shouldBe` 51
      height 2 1 `shouldBe` 1
      height 4 17 `shouldBe` 3213
      height 16 19 `shouldBe` 524096
      height 23 19 `shouldBe` 524287
    --

    it "should work for some advanced tests" $ do
      height 13 550 `shouldBe` 621773656
      height 531 550 `shouldBe` 424414512
    --

    it "should work for some serious tests :)" $ do
      height 10000 100000 `shouldBe` 132362171
      height 80000 100000 `shouldBe` 805097588
      height 3000 (2 ^ 200) `shouldBe` 141903106
      height 80000 40000 `shouldBe` 616494770
      height 40000 80000 `shouldBe` 303227698
    --

    it "should work for some random tests :)" $
      withMaxSuccess 40 $
        conjoin
          [ forAll (choose (1, 80000)) $ \n -> forAll (choose (1, 100000)) $ \m -> tst n m,
            forAll (choose (80000, 100000)) $ \m -> tst 80000 m,
            forAll (choose (1, 3000)) $ \n -> forAll (choose (1, 2 ^ 200)) $ \m -> tst n m
          ]