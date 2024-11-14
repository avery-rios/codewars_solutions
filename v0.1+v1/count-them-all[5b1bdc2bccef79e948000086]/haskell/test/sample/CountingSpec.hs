{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PolyKinds, KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module CountingSpec where
import Counting.Preloaded
import Counting (Count(..), Countable(count), Factor(factor), Listable(list))
import Test.Hspec
import Test.QuickCheck
import Data.Proxy
import Data.Void
import Data.Functor.Identity
import Control.Applicative (liftA2)
import Data.Kind (Type)
import Data.List (genericLength, nub)

instance Arbitrary Nat where arbitrary = toEnum . getNonNegative <$> arbitrary
instance Arbitrary (Count c) where arbitrary = Count <$> arbitrary
instance Arbitrary (Proxy a) where arbitrary = return Proxy

count' :: Countable c => Proxy c -> Count c
count' Proxy = count
factor' :: Factor f => Proxy f -> Count c -> Count (f c)
factor' Proxy = factor
list' :: Listable l => Proxy l -> [l]
list' Proxy = list

applyProxy :: Proxy (f :: k1 -> k) -> Proxy (x :: k1) -> Proxy (f x)
applyProxy Proxy Proxy = Proxy

applyProxy2 :: Proxy (f :: k1 -> k2 -> k) -> Proxy (x :: k1) -> Proxy (y :: k2) -> Proxy (f x y)
applyProxy2 Proxy Proxy Proxy = Proxy

type MonoGen (a :: k) = Gen (Proxy a)

data ACountable = forall c. Countable (c :: Type) => ACountable (Proxy c)
instance Show ACountable where
  show (ACountable p) = "Countable c => Proxy c where count' (Proxy c) = " ++ show (count' p)

simpleCountables :: Gen ACountable
simpleCountables = oneof [
  ACountable <$> (arbitrary :: MonoGen Void),
  ACountable <$> (arbitrary :: MonoGen ()),
  ACountable <$> (arbitrary :: MonoGen Bool)]

data AFactor = forall f. Factor (f :: Type -> Type) => AFactor (Proxy f)
instance Show AFactor where
  show (AFactor p) = "Factor f => Proxy f where factor' (Proxy f) (Count 1) = " ++ show (factor' p $ Count 1)

simpleFactors :: Gen AFactor
simpleFactors = oneof [
  AFactor <$> (arbitrary :: MonoGen Maybe),
  AFactor <$> (arbitrary :: MonoGen Identity),
  AFactor <$> (arbitrary :: MonoGen Proxy)]

factors :: Gen AFactor
factors = simpleFactors

countables :: Gen ACountable
countables = frequency [(1, simpleCountables), (9, liftA2 apply factors countables)] where
  apply (AFactor pf) (ACountable pc) = ACountable $ applyProxy pf pc

data AListable = forall (l :: Type). (Show l, Eq l, Listable l) => AListable (Proxy l)
instance Show AListable where
  show (AListable p) = "Listable l => Proxy l where list' (Proxy l) = " ++ show (list' p)

simpleListables :: Gen AListable
simpleListables = oneof [
  AListable <$> (arbitrary :: MonoGen Void),
  AListable <$> (arbitrary :: MonoGen ()),
  AListable <$> (arbitrary :: MonoGen Bool)]

listables :: Gen AListable
listables = simpleListables

forAllCountables :: Testable prop => (ACountable -> Count () -> prop) -> Property
forAllCountables f = forAll ((,) <$> countables <*> arbitrary) $ uncurry f

forAll2Factors :: Testable prop => (AFactor -> AFactor -> Count () -> prop) -> Property
forAll2Factors f = forAll ((,,) <$> factors <*> factors <*> arbitrary) $ \(a,b,c) -> f a b c

forAllListables :: Testable prop => (AListable -> AListable -> prop) -> Property
forAllListables f = forAll ((,) <$> listables <*> listables) $ uncurry f 

shouldMatchLength :: Listable l => Proxy l -> Expectation
shouldMatchLength p = genericLength (list' p) `shouldBe` getCount (count' p)

spec :: Spec
spec = do
  describe "Countable" $ do
    it "Bool" $ (count :: Count Bool) `shouldBe` Count 2
  describe "Factor" $ do
    it "Identity" $ property $ \c@(Count n) -> factor' (Proxy :: Proxy Identity) c `shouldBe` Count n
  describe "Listable" $ do
    it "Void" $ shouldMatchLength (Proxy :: Proxy Void)
    it "()" $ shouldMatchLength (Proxy :: Proxy ())
    it "Bool" $ (list :: [Bool]) `shouldMatchList` [False, True]
    describe "Maybe" $ do
      it "Maybe Void" $ shouldMatchLength (Proxy :: Proxy (Maybe Void))
      it "random tests" $ forAll listables $ \(AListable p) -> shouldMatchLength $ applyProxy (Proxy :: Proxy Maybe) p
    it "[()]" $ length (nub $ take 239 (list :: [[()]])) == 239 -- all distinct
    it "Either" $ forAllListables $ \(AListable pa) (AListable pb) -> shouldMatchLength $ applyProxy2 (Proxy :: Proxy Either) pa pb
    it "(,)" $ forAllListables $ \(AListable pa) (AListable pb) -> shouldMatchLength $ applyProxy2 (Proxy :: Proxy (,)) pa pb
    it "(->)" $ forAllListables $ \(AListable pa) (AListable pb) -> shouldMatchLength $ applyProxy2 (Proxy :: Proxy (->)) pa pb

main = hspec spec