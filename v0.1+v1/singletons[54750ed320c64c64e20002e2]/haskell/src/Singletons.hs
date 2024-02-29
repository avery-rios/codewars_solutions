{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Singletons where

import Prelude hiding (drop, head, map, replicate, tail, take, zipWith, (++))

data Vec a n where
  VNil :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

-- promoted to type level by data kinds
data Nat = Zero | Succ Nat

data SNat a where
  SZero :: SNat Zero
  SSucc :: SNat a -> SNat (Succ a)

type family (a :: Nat) :< (b :: Nat) :: Bool where
  m :< Zero = False
  Zero :< Succ n = True
  (Succ m) :< (Succ n) = m :< n

type family Add (a :: Nat) (b :: Nat) :: Nat where
  Add Zero b = b
  Add (Succ n) b = Succ (Add n b)

type family Sub (a :: Nat) (b :: Nat) :: Nat where
  Sub a Zero = a
  Sub Zero _ = Zero
  Sub (Succ a) (Succ b) = Sub a b

type family Min (a :: Nat) (b :: Nat) :: Nat where
  Min _ Zero = Zero
  Min Zero _ = Zero
  Min (Succ a) (Succ b) = Succ (Min a b)

map :: (a -> b) -> Vec a n -> Vec b n
map _ VNil = VNil
map f (VCons x xs) = VCons (f x) (map f xs)

index :: ((a :< b) ~ True) => SNat a -> Vec s b -> s
index SZero (VCons h _) = h
index (SSucc s) (VCons _ t) = index s t

replicate :: s -> SNat a -> Vec s a
replicate _ SZero = VNil
replicate i (SSucc s) = VCons i (replicate i s)

-- Both vectors must be of equal length
zipWith :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWith _ VNil VNil = VNil
zipWith f (VCons h1 t1) (VCons h2 t2) = VCons (f h1 h2) (zipWith f t1 t2)

(++) :: Vec v m -> Vec v n -> Vec v (Add m n)
VNil ++ b = b
VCons h t ++ b = VCons h (t ++ b)

-- The semantics should match that of take for normal lists.
take :: SNat a -> Vec s b -> Vec s (Min a b)
take SZero _ = VNil
take _ VNil = VNil
take (SSucc n) (VCons h t) = VCons h (take n t)

-- The semantics should match that of drop for normal lists.
drop :: SNat a -> Vec s b -> Vec s (Sub b a)
drop SZero v = v
drop _ VNil = VNil
drop (SSucc n) (VCons _ t) = drop n t

head :: Vec s (Succ n) -> s
head (VCons h _) = h

tail :: Vec s (Succ n) -> Vec s n
tail (VCons _ t) = t
