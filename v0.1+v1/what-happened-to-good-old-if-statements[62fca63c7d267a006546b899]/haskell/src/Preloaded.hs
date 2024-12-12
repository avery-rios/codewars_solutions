module Preloaded where

isDivisibleBy :: Integral a => a -> a -> Bool
isDivisibleBy n v = (n `mod` v) == 0
