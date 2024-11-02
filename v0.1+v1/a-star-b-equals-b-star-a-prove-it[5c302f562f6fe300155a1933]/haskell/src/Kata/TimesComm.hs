{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Kata.TimesComm (timesComm) where

import Data.Type.Equality
import Kata.TimesComm.Definitions

reflexive :: Natural n -> Equal n n
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS (reflexive n)

plusZr :: Natural a -> a :~: (a :+: Z)
plusZr NumZ = Refl
plusZr (NumS n) =
  case plusZr n of
    Refl -> Refl

plusSb :: Natural a -> Natural b -> S (a :+: b) :~: (a :+: S b)
plusSb NumZ _ = Refl
plusSb (NumS a) b = case plusSb a b of
  Refl -> Refl

plusCommE :: Natural a -> Natural b -> (a :+: b) :~: (b :+: a)
plusCommE NumZ b = plusZr b
plusCommE (NumS a) b =
  case plusCommE b a of
    Refl -> plusSb b a

plusAssocE :: Natural a -> Natural b -> Natural c -> (a :+: (b :+: c)) :~: ((a :+: b) :+: c)
plusAssocE NumZ _ _ = Refl
plusAssocE (NumS a) b c =
  case plusAssocE a b c of
    Refl -> Refl

plusN :: Natural a -> Natural b -> Natural (a :+: b)
plusN NumZ b = b
plusN (NumS a) b = NumS (plusN a b)

timesN :: Natural a -> Natural b -> Natural (a :*: b)
timesN NumZ _ = NumZ
timesN (NumS a) b = plusN b (timesN a b)

-- This will also be helpful
zeroComm :: Natural a -> Z :~: (a :*: Z)
zeroComm NumZ = Refl
zeroComm (NumS a) = zeroComm a

timesSb :: Natural a -> Natural b -> (b :+: (b :*: a)) :~: (b :*: S a)
timesSb a NumZ = case zeroComm a of
  Refl -> Refl
timesSb a (NumS b) =
  case plusAssocE b a (b `timesN` a) of
    Refl -> case plusCommE a b of
      Refl -> case plusAssocE a b (b `timesN` a) of
        Refl -> case timesSb a b of
          Refl -> Refl

-- This is the proof that the kata requires.

timesCommE :: Natural a -> Natural b -> (a :*: b) :~: (b :*: a)
timesCommE NumZ b = zeroComm b
timesCommE (NumS a) b =
  case timesSb a b of
    Refl -> case timesCommE a b of
      Refl -> Refl

-- | a * b = b * a
timesComm :: Natural a -> Natural b -> Equal (a :*: b) (b :*: a)
timesComm a b = case timesCommE a b of
  Refl -> reflexive (timesN a b)
