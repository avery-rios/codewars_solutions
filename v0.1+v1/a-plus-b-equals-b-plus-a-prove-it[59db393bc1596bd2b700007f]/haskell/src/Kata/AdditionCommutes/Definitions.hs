{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Kata.AdditionCommutes.Definitions where

import Data.Kind

data Z

data S n

data Natural :: Type -> Type where
  NumZ :: Natural Z
  NumS :: Natural n -> Natural (S n)

data Equal :: Type -> Type -> Type where
  EqlZ :: Equal Z Z
  EqlS :: Equal n m -> Equal (S n) (S m)

type family (:+:) (n :: Type) (m :: Type) :: Type where
  Z :+: m = m
  S n :+: m = S (n :+: m)
