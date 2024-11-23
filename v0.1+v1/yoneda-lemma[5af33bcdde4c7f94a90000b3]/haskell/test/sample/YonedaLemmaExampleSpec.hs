{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module YonedaLemmaExampleSpec where
import YonedaLemma
import YonedaLemmaPreloaded
import Data.Proxy
import Test.Hspec
import Test.QuickCheck

save :: Int -> Nat (Hom Int) ((,) String)
save i ix = ("pocket", ix i)

instance Factor Maybe where
  factor' proxy = mapC (1+) $ count' proxy
{- in Preloaded (truth now)
class Countable c where
  count' :: Proxy c -> Count c
  count :: Count c

class Factor f where
  factor' :: Countable c => Proxy c -> Count (f c)
  factor :: Countable c => Count (f c)

mapC :: (Int -> Int) -> Count a -> Count b
liftC2 :: (Int -> Int -> Int) -> Count a -> Count b -> Count c
coerce :: Count a -> Count b
-}
-- with them you could (if you want) create your own machinery
-- for challenges, as in Test Cases

spec :: Spec
spec = do
  describe "saving" $ do
    it "could save 'to' pocket" $ do
      property $ \i -> to (save i) `shouldBe` ("pocket", i)
  describe "counting" $ do
    it "challenge1" $ challenge1 `shouldBe` count1

main = hspec spec