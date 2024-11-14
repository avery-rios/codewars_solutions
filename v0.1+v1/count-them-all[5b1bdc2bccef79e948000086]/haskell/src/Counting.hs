{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Counting where

import Counting.Preloaded
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import Data.Functor.Identity (Identity)
import Data.Functor.Product (Product)
import Data.Functor.Sum (Sum)
import Data.Kind (Type)
import qualified Data.List as L
import Data.Maybe (fromJust)
import Data.Proxy (Proxy)
import Data.Void (Void)

newtype Count x = Count {getCount :: Nat} deriving (Show, Eq, Ord)

-- | helper functions
mapC :: (Nat -> Nat) -> Count a -> Count b
mapC f (Count c) = Count (f c)

liftC2 :: (Nat -> Nat -> Nat) -> Count a -> Count b -> Count c
liftC2 f (Count a) (Count b) = Count (f a b)

coerceC :: Count a -> Count b
coerceC = coerce

-- | Countable
class Countable (c :: Type) where
  count :: Count c

instance Countable Void where count = Count Z

instance Countable () where count = Count 1

instance Countable Bool where count = Count 2

instance Countable Nat where count = mapC S (count @Nat)

-- | Factor
class Factor (f :: Type -> Type) where
  factor :: Count c -> Count (f c)

instance (Factor f, Countable c) => Countable (f c) where
  count = factor (count @c)

instance Factor Maybe where factor = mapC S

instance Factor Identity where factor = coerceC

instance Factor Proxy where factor _ = Count (S Z)

instance Factor Count where factor _ = coerceC (count @Nat)

instance Factor [] where
  factor v@(Count nv) =
    mapC (\cnt -> S (nv * cnt)) (factor @[] v)

instance (Countable c) => Factor (Const c) where
  factor _ = coerceC (count @c)

instance (Countable c) => Factor (Either c) where
  factor = liftC2 (+) (count @c)

instance (Countable c) => Factor ((,) c) where
  factor = liftC2 (*) (count @c)

instance (Countable c) => Factor ((->) c) where
  factor = liftC2 (\e b -> b ^ e) (count @c)

instance (Factor f, Factor g) => Factor (Sum f g) where
  factor v = liftC2 (+) (factor @f v) (factor @g v)

instance (Factor f, Factor g) => Factor (Product f g) where
  factor v = liftC2 (*) (factor @f v) (factor @g v)

instance (Factor f, Factor g) => Factor (Compose f g) where
  factor v = coerceC (factor @f (factor @g v))

-- | Listable
class (Countable a) => Listable (a :: Type) where
  list :: [a]

instance Listable Void where list = []

instance Listable () where list = [()]

instance Listable Bool where list = [True, False]

instance Listable Nat where list = Z : fmap S list

instance (Listable c) => Listable (Maybe c) where
  list = Nothing : fmap Just (list @c)

instance (Listable c) => Listable [c] where
  list = [] : concat [(c :) <$> list @[c] | c <- list @c]

instance (Listable a, Listable b) => Listable (Either a b) where
  list = fmap Left (list @a) ++ fmap Right (list @b)

instance (Listable a, Listable b) => Listable (a, b) where
  list = [(a, b) | a <- list @a, b <- list @b]

instance (Eq a, Listable a, Listable b) => Listable (a -> b) where
  list = case count @b of
    Count Z -> case count @a of
      Count Z -> [undefined]
      _ -> []
    _ ->
      fmap
        (\l va -> fromJust (L.lookup va l))
        (zip (list @a) <$> listLen (getCount (count @a)))
    where
      listB = list @b

      listLen Z = [[]]
      listLen (S v) = [h : t | h <- listB, t <- listLen v]
