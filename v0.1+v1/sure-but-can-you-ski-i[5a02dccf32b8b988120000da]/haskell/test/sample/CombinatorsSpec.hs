{-# LANGUAGE GADTs, RankNTypes #-}
module CombinatorsSpec where
import Combinators
import PredefinedCombinators (SKI(..))
import Test.Hspec
import Test.QuickCheck

spec :: Spec
spec = do
  describe "Type check" $ do
      it "should compile" $ 1 `shouldBe` 1