{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module YonedaLemmaPreloaded where

import qualified Data.Coerce as D
import Data.Proxy

newtype Count x = Count {getCount :: Int} deriving (Show, Eq)

class Countable c where
  count :: Count c
  count = count' (Proxy @c)

  count' :: proxy c -> Count c
  count' _ = count @c

class Factor f where
  factor :: forall c. (Countable c) => Count (f c)
  factor = factor' (Proxy @c)

  factor' :: forall c proxy. (Countable c) => proxy c -> Count (f c)
  factor' _ = factor @f @c

instance (Factor f, Countable c) => Countable (f c) where count = factor

mapC :: (Int -> Int) -> Count a -> Count b
mapC f (Count v) = Count (f v)

liftC2 :: (Int -> Int -> Int) -> Count a -> Count b -> Count c
liftC2 f (Count l) (Count r) = Count (f l r)

coerce :: Count a -> Count b
coerce = D.coerce
