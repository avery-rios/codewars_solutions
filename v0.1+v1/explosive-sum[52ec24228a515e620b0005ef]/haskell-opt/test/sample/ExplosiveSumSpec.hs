module ExplosiveSumSpec where
import ExplosiveSum
import Test.Hspec

main = hspec spec

spec = do
  describe "explosiveSum" $ do
    it "should work for some basic tests" $ do
      explosiveSum 1    `shouldBe` 1
      explosiveSum 2    `shouldBe` 2
      explosiveSum 3    `shouldBe` 3
      explosiveSum 4    `shouldBe` 5
      explosiveSum 5    `shouldBe` 7
      explosiveSum 20   `shouldBe` 627
      explosiveSum 30   `shouldBe` 5604
      explosiveSum 40   `shouldBe` 37338
      explosiveSum 43   `shouldBe` 63261
      explosiveSum 60   `shouldBe` 966467
      explosiveSum 275  `shouldBe` 1520980492851175