{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Kata.AdditionCommutes (plusCommutes) where

import Data.Type.Equality
import Kata.AdditionCommutes.Definitions
  ( Equal (..),
    Natural (..),
    S,
    Z,
    (:+:),
  )

plusZr :: Natural a -> a :~: (a :+: Z)
plusZr NumZ = Refl
plusZr (NumS n) =
  case plusZr n of
    Refl -> Refl

plusSb :: Natural a -> Natural b -> S (a :+: b) :~: (a :+: S b)
plusSb NumZ _ = Refl
plusSb (NumS a) b = case plusSb a b of
  Refl -> Refl

plusComm :: Natural a -> Natural b -> (a :+: b) :~: (b :+: a)
plusComm NumZ b = plusZr b
plusComm (NumS a) b =
  case plusComm b a of
    Refl -> plusSb b a

reflexive :: Natural n -> Equal n n
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS (reflexive n)

plusN :: Natural a -> Natural b -> Natural (a :+: b)
plusN NumZ b = b
plusN (NumS a) b = NumS (plusN a b)

-- | a + b = b + a
plusCommutes :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
plusCommutes a b =
  case plusComm a b of
    Refl -> reflexive (plusN a b)
