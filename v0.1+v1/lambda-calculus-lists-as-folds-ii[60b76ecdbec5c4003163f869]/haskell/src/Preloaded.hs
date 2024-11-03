{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}

module Preloaded
  ( P.undefined,
    (P.$),
    List (..),
    Number,
    zero,
    succ,
    pred,
    plus,
    times,
    Boolean,
    true,
    false,
    (?),
    or,
    and,
    not,
    Option,
    nothing,
    just,
    option,
    fmap,
    Pair,
    pair,
    uncurry,
    fst,
    snd,
    first,
    second,
    both,
    double,
  )
where

import Data.Word (Word64)
import Prelude (Bool (..), Maybe (..), (&&), (*), (+), (-), (||))
import qualified Prelude as P

newtype List a = List {foldr :: forall z. (a -> z -> z) -> z -> z}

newtype Number = Number Word64
  deriving (P.Show, P.Eq, P.Ord, P.Num, P.Enum, P.Real, P.Integral)

zero :: Number -> Boolean
zero (Number 0) = true
zero _ = false

succ :: Number -> Number
succ (Number a) = Number (a + 1)

pred :: Number -> Number
pred (Number 0) = Number 0
pred (Number n) = Number (n - 1)

plus :: Number -> Number -> Number
plus (Number a) (Number b) = Number (a + b)

times :: Number -> Number -> Number
times (Number a) (Number b) = Number (a * b)

newtype Boolean = Boolean Bool

true :: Boolean
true = Boolean True

false :: Boolean
false = Boolean False

(?) :: Boolean -> z -> z -> z
(?) (Boolean True) t _ = t
(?) (Boolean False) _ f = f

or :: Boolean -> Boolean -> Boolean
or (Boolean l) (Boolean r) = Boolean (l || r)

and :: Boolean -> Boolean -> Boolean
and (Boolean l) (Boolean r) = Boolean (l && r)

not :: Boolean -> Boolean
not (Boolean True) = Boolean False
not (Boolean False) = Boolean True

newtype Option a = Option (Maybe a)

nothing :: Option a
nothing = Option Nothing

just :: a -> Option a
just v = Option (Just v)

option :: Option a -> b -> (a -> b) -> b
option (Option a) n f = P.maybe n f a

fmap :: (t -> a) -> Option t -> Option a
fmap _ (Option Nothing) = Option Nothing
fmap f (Option (Just v)) = Option (Just (f v))

newtype Pair a b = Pair (a, b)

pair :: a -> b -> Pair a b
pair a b = Pair (a, b)

uncurry :: Pair t1 t2 -> (t1 -> t2 -> t3) -> t3
uncurry (Pair (a, b)) f = f a b

fst :: Pair a b -> a
fst (Pair (a, _)) = a

snd :: Pair a b -> b
snd (Pair (_, b)) = b

first :: (t -> a) -> Pair t b -> Pair a b
first f (Pair (a, b)) = Pair (f a, b)

second :: (t -> b) -> Pair a t -> Pair a b
second f (Pair (a, b)) = Pair (a, f b)

both :: (t -> b) -> Pair t t -> Pair b b
both f (Pair (a, b)) = Pair (f a, f b)

double :: (t1 -> a) -> (t2 -> b) -> Pair t1 t2 -> Pair a b
double f g (Pair (a, b)) = Pair (f a, g b)