{-# LANGUAGE LambdaCase #-}

module ISO where

import Data.Bifunctor
import Data.Maybe
import Data.Void

-- Please copy your code of Isomorphism to here.

-- Sometimes, we can treat a Type as a Number:
-- if a Type t has n distinct value, it's Number is n.
-- This is formally called cardinality.
-- See https://en.wikipedia.org/wiki/Cardinality

-- Void has cardinality of 0 (we will abbreviate it Void is 0).
-- () is 1.
-- Bool is 2.
-- Maybe a is 1 + a.
-- We will be using peano arithmetic so we will write it as S a.
-- https://en.wikipedia.org/wiki/Peano_axioms
-- Either a b is a + b.
-- (a, b) is a * b.
-- a -> b is b ^ a. Try counting (() -> Bool) and (Bool -> ())

-- Algebraic data type got the name because
-- it satisfies a lot of algebraic rules under isomorphism

type ISO a b = (a -> b, b -> a)

-- given ISO a b, we can go from a to b
substL :: ISO a b -> (a -> b)
substL = fst

-- and vice versa
substR :: ISO a b -> (b -> a)
substR = snd

-- isomorphism is reflexive
refl :: ISO a a
refl = (id, id)

-- isomorphism is symmetric
symm :: ISO a b -> ISO b a
symm (ab, ba) = (ba, ab)

-- isomorphism is transitive
trans :: ISO a b -> ISO b c -> ISO a c
trans (ab, ba) (bc, cb) = (bc . ab, ba . cb)

-- We can combine isomorphism:
isoTuple :: ISO a b -> ISO c d -> ISO (a, c) (b, d)
isoTuple (ab, ba) (cd, dc) =
  (bimap ab cd, bimap ba dc)

isoList :: ISO a b -> ISO [a] [b]
isoList (ab, ba) = (fmap ab, fmap ba)

isoMaybe :: ISO a b -> ISO (Maybe a) (Maybe b)
isoMaybe (ab, ba) = (fmap ab, fmap ba)

isoEither :: ISO a b -> ISO c d -> ISO (Either a c) (Either b d)
isoEither (ab, ba) (cd, dc) = (bimap ab cd, bimap ba dc)

isoFunc :: ISO a b -> ISO c d -> ISO (a -> c) (b -> d)
isoFunc (ab, ba) (cd, dc) = (\f -> cd . f . ba, \g -> dc . g . ab)

isoSymm :: ISO (ISO a b) (ISO b a)
isoSymm = (symm, symm)

-- a = b -> c = d -> a * c = b * d
isoProd :: ISO a b -> ISO c d -> ISO (a, c) (b, d)
isoProd (ab, ba) (cd, dc) = (bimap ab cd, bimap ba dc)

-- a = b -> c = d -> a + c = b + d
isoPlus :: ISO a b -> ISO c d -> ISO (Either a c) (Either b d)
isoPlus (ab, ba) (cd, dc) = (bimap ab cd, bimap ba dc)

-- a = b -> S a = S b
isoS :: ISO a b -> ISO (Maybe a) (Maybe b)
isoS (ab, ba) = (fmap ab, fmap ba)

-- a = b -> c = d -> c ^ a = d ^ b
isoPow :: ISO a b -> ISO c d -> ISO (a -> c) (b -> d)
isoPow (ab, ba) (cd, dc) = (\f -> cd . f . ba, \g -> dc . g . ab)

-- a + b = b + a
plusComm :: ISO (Either a b) (Either b a)
plusComm = (swap, swap)
  where
    swap = either Right Left

-- a + b + c = a + (b + c)
plusAssoc :: ISO (Either (Either a b) c) (Either a (Either b c))
plusAssoc =
  ( \case
      Left (Left a) -> Left a
      Left (Right b) -> Right (Left b)
      Right c -> Right (Right c),
    \case
      Left a -> Left (Left a)
      Right (Left b) -> Left (Right b)
      Right (Right c) -> Right c
  )

-- a * b = b * a
multComm :: ISO (a, b) (b, a)
multComm = (swap, swap)
  where
    swap (a, b) = (b, a)

-- a * b * c = a * (b * c)
multAssoc :: ISO ((a, b), c) (a, (b, c))
multAssoc = (\((a, b), c) -> (a, (b, c)), \(a, (b, c)) -> ((a, b), c))

-- dist :: a * (b + c) = a * b + a * c
dist :: ISO (a, Either b c) (Either (a, b) (a, c))
dist =
  ( \(a, bc) -> case bc of
      Left b -> Left (a, b)
      Right c -> Right (a, c),
    \case
      Left (a, b) -> (a, Left b)
      Right (a, c) -> (a, Right c)
  )

-- (c ^ b) ^ a = c ^ (a * b)
curryISO :: ISO (a -> b -> c) ((a, b) -> c)
curryISO = (uncurry, curry)

-- 1 = S O (we are using peano arithmetic)
-- https://en.wikipedia.org/wiki/Peano_axioms
one :: ISO () (Maybe Void)
one = (const Nothing, const ())

-- 2 = S (S O)
two :: ISO Bool (Maybe (Maybe Void))
two =
  ( \case
      True -> Just ()
      False -> Nothing,
    isJust
  )
    `trans` isoS one

-- O + b = b
plusO :: ISO (Either Void b) b
plusO = (left, Right)
  where
    left (Left x) = absurd x -- absurd :: Void -> a
    left (Right x) = x

-- S a + b = S (a + b)
plusS :: ISO (Either (Maybe a) b) (Maybe (Either a b))
plusS =
  ( \case
      Left (Just a) -> Just (Left a)
      Left Nothing -> Nothing
      Right b -> Just (Right b),
    \case
      Just (Left a) -> Left (Just a)
      Just (Right b) -> Right b
      Nothing -> Left Nothing
  )

-- 1 + b = S b
plusSO :: ISO (Either () b) (Maybe b)
plusSO = isoPlus one refl `trans` plusS `trans` isoS plusO

-- O * a = O
multO :: ISO (Void, a) Void
multO = (fst, absurd)

-- S a * b = b + a * b
multS :: ISO (Maybe a, b) (Either b (a, b))
multS =
  ( \(ma, b) -> case ma of
      Just a -> Right (a, b)
      Nothing -> Left b,
    \case
      Left b -> (Nothing, b)
      Right (a, b) -> (Just a, b)
  )

-- 1 * b = b
multSO :: ISO ((), b) b
multSO =
  isoProd one refl
    `trans` multS
    `trans` isoPlus refl multO
    `trans` plusComm
    `trans` plusO

-- a ^ O = 1
powO :: ISO (Void -> a) ()
powO = (const (), const absurd)

-- a ^ (S b) = a * (a ^ b)
powS :: ISO (Maybe b -> a) (a, b -> a)
powS =
  ( \f -> (f Nothing, f . Just),
    \(a, g) -> \case
      Just b -> g b
      Nothing -> a
  )

-- a ^ 1 = a
-- Go the hard way (like multSO, plusSO)
-- to prove that you really get what is going on!
powSO :: ISO (() -> a) a
powSO =
  isoPow one refl
    `trans` powS
    `trans` isoProd refl powO
    `trans` multComm
    `trans` multSO

-- Here's a trick:
-- replace undefined with the rhs of the comment on previous line
-- When you're not sure what to fill in for a value,
-- Have it as a _
-- GHC will goes like
-- "Found hole `_' with type: ISO (() -> a) (Maybe b0 -> a0)"
-- So you can immediately see value of what type are needed
-- This process can be repeat indefinitely -
-- For example you might replace `_` with `isoFunc _ _`
-- So GHC hint you on more specific type.
-- This is especially usefull if you have complex type.
-- See https://wiki.haskell.org/GHC/Typed_holes
-- And "stepwise refinement" for more details.
