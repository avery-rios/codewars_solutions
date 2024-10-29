module PolynomFieldSpec (spec) where

import Control.Applicative
import Control.Monad
import Data.Function
import Data.List
import Data.Ord

import Test.Hspec
import Test.QuickCheck
import PolynomField

spec = do
    describe "polyFromPowers" $ do
        it "empty list equals zero" $ polyFromPowers [] == zero
        it "list order of polyFromPowers does not matter" $ polyFromPowers [1, 2, 3] `shouldBe` polyFromPowers [2, 3, 1]
    describe "show" $ do
        it "0" $ show zero `shouldBe` "0"
        it "x^8" $ show (polyFromDeg 8) `shouldBe` "x^8"
        it "x^2 + x^1" $ show (polyFromPowers [2, 1]) `shouldBe` "x^2 + x^1"
    describe "degree of polynoms" $ do
        it "deg(zero) = -1" $ deg zero `shouldBe` (-1)
        it "deg(one) = 0" $ deg one `shouldBe` 0
        it "deg(x^n) = n" $ property $ forAll gen15 $ \n -> deg (polyFromDeg n) `shouldBe` n
        it "deg(x^5 + x^2) = 5" $ deg (polyFromPowers [5, 2]) `shouldBe` 5
    describe "addition" $ do
        it "x^n + x^n = 0" $ property $ forAll gen15 $ \i ->
            let p = polyFromDeg i
            in p .+. p == zero
        it "(x^2 + x^1) + (x^3 + x^2) = x^3 + x^1" $ (polyFromPowers [2, 1] .+. polyFromPowers [3, 2]) `shouldBe` polyFromPowers [3, 1]
    describe "ring multiplication" $ do
        it "x^n * x^m = x^{n + m}" $ property $ forAll (twoOf gen7) $ \(ld, rd) ->
            (polyFromDeg ld `multiply` polyFromDeg rd) == polyFromDeg (ld + rd)
    describe "polyDivMod" $ do
        it "(x^2 + x^1) `polyDivMod` (x^4 + x^3) = (0, x^2 + x^1)" $
            (polyFromPowers [1, 2] `polyDivMod` polyFromPowers [3, 4]) `shouldBe` (zero, polyFromPowers [1, 2])
        it "some poly division" $ (polyFromPowers [2, 1] `polyDivMod` polyFromPowers [1, 0]) `shouldBe` (polyFromDeg 1, zero)
    describe "field multiplication" $
        it "some poly field mult" $
            polyFromPowers [4, 2, 1] .*. polyFromPowers [4] `shouldBe` polyFromPowers [6, 5, 4, 3, 1, 0]

  where
    powerGen = do
        n <- gen7
        nub <$> vectorOf n gen7

    gen15    = choose (0, 16)
    gen7     = choose (0, 8)
    twoOf g  = liftM2 (,) g g