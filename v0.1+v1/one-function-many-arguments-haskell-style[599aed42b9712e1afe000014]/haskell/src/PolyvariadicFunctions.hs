{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module PolyvariadicFunctions where

class PolyAdd a where
  contA :: Int -> a

instance PolyAdd Int where
  contA = id

instance (a ~ Int, PolyAdd r) => PolyAdd (a -> r) where
  contA v1 v2 = contA (v1 + v2)

-- `polyAdd` sums its arguments, all `Int`s.
polyAdd :: (PolyAdd a) => a
polyAdd = contA 0

class PolyList r a | a -> r where
  contL :: [r] -> a

instance PolyList r [r] where
  contL = reverse

instance (PolyList r a) => PolyList r (r -> a) where
  contL l e = contL (e : l)

-- | `polyList` turns its arguments into a list, polymorphically.
polyList :: forall r a. (PolyList r a) => a
polyList = contL @r @a []

class PolyWords a where
  contW :: [String] -> a

instance PolyWords String where
  contW = unwords . reverse

instance (PolyWords r) => PolyWords (String -> r) where
  contW acc s = contW (s : acc)

-- | `polyWords` turns its arguments into a spaced string.
polyWords :: (PolyWords r) => r
polyWords = contW []
