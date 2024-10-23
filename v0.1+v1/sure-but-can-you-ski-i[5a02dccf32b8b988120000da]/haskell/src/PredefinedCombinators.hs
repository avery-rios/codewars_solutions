{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module PredefinedCombinators where

import Data.Kind (Type)

data SKI :: Type -> Type where
  Ap :: SKI (a -> b) -> SKI a -> SKI b
  S :: SKI ((a -> b -> c) -> (a -> b) -> a -> c)
  K :: SKI (a -> b -> a)
  I :: SKI (a -> a)
