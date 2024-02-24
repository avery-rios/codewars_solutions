module SumOfIntervals (sumOfIntervals) where

import qualified Data.List as L

sumI :: Int -> Int -> [(Int, Int)] -> Int
sumI _ acc [] = acc
sumI r acc ((l0, r0) : rs)
  | r >= r0 = sumI r acc rs
  | otherwise = sumI r0 (acc + (r0 - max r l0)) rs

sumOfIntervals :: [(Int, Int)] -> Int
sumOfIntervals rs =
  case L.sort rs of
    [] -> 0
    (l0, r0) : r -> sumI r0 (r0 - l0) r
