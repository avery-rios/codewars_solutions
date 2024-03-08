{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module PC where

type ISO a b = (a -> b, b -> a)

-- See https://www.codewars.com/kata/isomorphism

symm :: ISO a b -> ISO b a
symm (ab, ba) = (ba, ab)

substL :: ISO a b -> (a -> b)
substL = fst

substR :: ISO a b -> (b -> a)
substR = snd

liftISO2 :: ISO a b -> ISO (a -> a -> a) (b -> b -> b)
liftISO2 (ab, ba) =
  ( \f b1 b2 -> ab (f (ba b1) (ba b2)),
    \g a1 a2 -> ba (g (ab a1) (ab a2))
  )

-- A Natural Number is either Zero,
-- or a Successor (1 +) of Natural Number.
-- We have (+)/(*) on Natural Number, or (-) it.
-- Since Natrual Number do not have negative, forall x, 0 - x = 0.
-- We also have pow on Natrual Number
-- Since Haskell is lazy, we also have infinity

class Nat n where
  zero :: n
  successor :: n -> n
  nat :: a -> (n -> a) -> n -> a -- Pattern Matching
  iter :: a -> (a -> a) -> n -> a -- Induction
  plus, minus, mult, pow :: n -> n -> n
  inf :: n
  inf = successor inf
  divide :: n -> n -> n
  l `divide` r
    | l == 0 && r == 0 = undefined
    | l < r = 0
    | otherwise = successor $ (l `minus` r) `divide` r

  -- notice (l `divide` 0) when l is not 0 will return inf
  isoP :: ISO n Peano -- See below for the definition of Peano
  isoP = (iter zero successor, iter zero successor)
  toP :: n -> Peano
  toP = substL isoP

instance {-# OVERLAPPABLE #-} (Nat n) => Show n where
  show = show . toP

instance {-# OVERLAPPABLE #-} (Nat n) => Eq n where
  l == r = toP l == toP r

instance {-# OVERLAPPABLE #-} (Nat n) => Ord n where
  l `compare` r = toP l `compare` toP r

instance {-# OVERLAPPABLE #-} (Nat n) => Num n where
  abs = id
  signum = nat zero (const 1)
  fromInteger 0 = zero
  fromInteger n | n > 0 = successor $ fromInteger (n - 1)
  (+) = plus
  (*) = mult
  (-) = minus

-- We can encode Natrual Number directly as Algebraic Data Type(ADT).
data Peano = O | S Peano deriving (Show, Eq, Ord)

-- Remember, 0 - x = 0 for all x.
instance Nat Peano where
  zero = O
  successor = S

  nat i _ O = i
  nat _ f (S n) = f n

  iter i _ O = i
  iter i f (S a) = f (iter i f a)

  plus O b = b
  plus (S a) b = S (plus a b)

  minus O _ = O
  minus a O = a
  minus (S a) (S b) = minus a b

  mult O _ = O
  mult (S a) b = plus b (mult a b)

  pow _ O = S O
  pow a (S b) = mult a (pow a b)

-- Peano is very similar to a basic data type in Haskell - List!
-- O is like [], and S is like :: (except it lack the head part)
-- When we want to store no information, we can use (), a empty tuple
-- This is different from storing nothing (called Void in Haskell),
-- as we can create a value of () by using (),
-- but we cannot create a value of Void.

-- Notice how you can implement everything once you have isoP,
-- By converting to Peano and using Nat Peano?
-- Dont do that. You wont learn anything.
-- Try to use operation specific to list.
instance Nat [()] where
  zero = []
  successor = (() :)

  nat i _ [] = i
  nat _ f (_ : t) = f t

  iter i _ [] = i
  iter i f (_ : t) = f (iter i f t)

  plus = (++)

  minus [] _ = []
  minus a [] = a
  minus (_ : a) (_ : b) = minus a b

  mult [] _ = []
  mult (_ : a) b = plus b (mult a b)

  pow _ [] = [()]
  pow a (_ : b) = mult a (pow a b)

-- Instead of defining Nat from zero, sucessor (and get Peano),
-- We can define it from Pattern Matching
newtype Scott = Scott {runScott :: forall a. a -> (Scott -> a) -> a}

instance Nat Scott where
  zero = Scott (\a _ -> a)
  successor n = Scott (\_ f -> f n)

  nat i f (Scott g) = g i f

  iter i f (Scott g) = g i (f . iter i f)

  -- Other operation on Scott numeral is sort of boring,
  -- So we implement it using operation on Peano.
  -- You shouldnt do this - I had handled all the boring case for you.
  plus = substR (liftISO2 isoP) plus
  minus = substR (liftISO2 isoP) minus
  mult = substR (liftISO2 isoP) mult
  pow = substR (liftISO2 isoP) pow

-- Or from induction!
newtype Church = Church {runChurch :: forall a. (a -> a) -> a -> a}

predC :: Church -> Church
predC (Church n) = Church (\f i -> fst (n (\(_, b) -> (b, f b)) (i, i)))

instance Nat Church where
  zero = Church (\_ a -> a)
  successor (Church n) = Church (\f i -> f (n f i))

  nat i f (Church n) =
    maybe
      i
      f
      ( n
          ( \case
              Nothing -> Just zero -- S O
              Just v -> Just (successor v) -- S (S _)
          )
          Nothing
      )
  iter i f (Church n) = n f i

  plus (Church a) (Church b) = Church (\f i -> a f (b f i))
  minus a (Church b) = b predC a
  mult (Church a) (Church b) = Church (\f i -> a (b f) i)
  pow (Church a) (Church b) = Church (\f i -> b (\h -> a h) f i)

-- Try to implement the calculation (except minus) in the primitive way.
-- Implement them by constructing Church explicitly.
-- So plus should not use successor,
-- mult should not use plus,
-- exp should not use mult.
