{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module YonedaLemma where

import Data.Functor.Contravariant
import Data.Void
import YonedaLemmaPreloaded

-- Hom(a, b) ≡ all arrows/morphisms from object `a` to object `b`
-- in given category.
-- Hom(a, -) covariant functor:
type Hom a = (->) a

-- natural transformation from functor f to functor g:
type Nat f g = forall x. f x -> g x

-- in order to witness isomorphism
-- we should provide `to` and `from` such, that
-- to . from ≡ id[f a]
-- from . to ≡ id[Nat (Hom a) f]
to :: (Functor f) => Nat (Hom a) f -> f a
to n = n id

from :: (Functor f) => f a -> Nat (Hom a) f
from fa f = fmap f fa

-- Hom(-, a) contravariant functor:
type CoHom a = Op a

to' :: (Contravariant f) => Nat (CoHom a) f -> f a
to' n = n (Op id)

from' :: (Contravariant f) => f a -> Nat (CoHom a) f
from' fa f = contramap (getOp f) fa

-- now we will try to count the natural transformations

-- | NOTE: from here onwards you should imagine `forall x` inside `Count (...)`,
-- | i. e., not `Count ((Numbers -> x) -> Maybe x)`, but `Count (forall x. (Numbers -> x) -> Maybe x)`
-- | we are unable to write it because GHC doesn't yet support impredicative polymorphism (see issue: https://www.codewars.com/kata/yoneda-lemma/discuss/haskell#5b0f4afd3aa7cf7eb100000e)
count1 :: forall f c x. (Functor f, Factor f, Countable c) => Count ((c -> x) -> f x)
count1 = coerce (factor @f @c)

-- |
-- > forall x. (x -> c) -> f x
-- > forall x. (Op c) x -> f x
-- > f c
count2 :: forall f c x. (Contravariant f, Factor f, Countable c) => Count ((x -> c) -> f x)
count2 = coerce (factor @f @c)

-- | TIP: you could use types `f`, `c` in RHS of count1 and count2
-- | (because of ScopedTypeVariables pragma and explicit forall)

-- and now i encourage you to count something on fingers ;)
data Numbers = One | Two | Three deriving (Show, Eq)

instance Countable Numbers where
  count = Count 3

newtype WMaybe a = WMaybe (Maybe a)
  deriving (Functor)

instance Factor WMaybe where
  factor :: forall c. (Countable c) => Count (WMaybe c)
  factor = coerce (Count (1 + getCount (count @c)))

challenge1 :: Count ((Numbers -> x) -> Maybe x)
challenge1 = coerce (count1 @WMaybe @Numbers)

challenge2 :: Count ((Maybe Numbers -> x) -> x)
challenge2 = coerce (factor @WMaybe @Numbers)

-- | isomorphic to @Bool->Numbers@
--
-- > forall x. (Numbers -> x) -> (Bool -> x)
-- > forall x. Bool -> ((Numbers -> x) -> x)
-- > Bool -> Numbers
challenge3 :: Count ((Numbers -> x) -> (Bool -> x))
challenge3 = Count 9 -- 3^2

-- | isomorphic to @Void->Bool@
challenge4 :: Count ((x -> Void) -> Predicate x)
challenge4 = Count 1 -- 2^0

-- | challenge5 :: Count (forall x. (x -> (forall y. (Bool -> y) -> (Numbers -> y))) -> (x -> Numbers))
--
-- > forall x. (x -> (forall y. (Bool -> y) -> (Numbers -> y))) -> (x -> Numbers)
-- > forall x. (x -> (forall y. Numbers -> (Bool -> y) -> y)) -> (x -> Numbers)
-- > forall x. (x -> (Numbers -> Bool)) -> (x -> Numbers)
-- > forall x. CoHom (Numbers -> Bool) x -> (Op Numbers) x
-- > Op Numbers (Numbers -> Bool)
-- > (Numbers -> Bool) -> Numbers
--
-- isomorphic to @(Numbers->Bool)->Numbers@
challenge5 :: Count ((x -> ((Bool -> y) -> (Numbers -> y))) -> (x -> Numbers))
challenge5 = Count (3 `iPow` (2 `iPow` 3))
  where
    iPow :: Int -> Int -> Int
    iPow = (^)
