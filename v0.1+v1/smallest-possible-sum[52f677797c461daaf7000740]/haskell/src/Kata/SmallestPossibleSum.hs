module Kata.SmallestPossibleSum (smallestPossibleSum) where

import Data.Foldable

smallestPossibleSum :: (Integral a) => [a] -> a
smallestPossibleSum [] = 0
smallestPossibleSum (x : xs) = fromIntegral (1 + length xs) * foldl' gcd x xs
