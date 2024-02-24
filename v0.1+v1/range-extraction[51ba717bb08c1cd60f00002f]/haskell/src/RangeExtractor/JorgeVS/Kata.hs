module RangeExtractor.JorgeVS.Kata (solution) where

import Data.Foldable

ranges :: [Integer] -> [(Integer, Integer)]
ranges =
  foldr'
    ( \i rs -> case rs of
        [] -> [(i, i)]
        (l, r) : rt
          | l == i + 1 -> (i, r) : rt
          | otherwise -> (i, i) : rs
    )
    []

formatRange :: (Integer, Integer) -> ShowS
formatRange (l, r)
  | l == r = shows l
  | r == l + 1 = shows l . (',' :) . shows r
  | otherwise = shows l . ('-' :) . shows r

format :: [(Integer, Integer)] -> ShowS
format [] = id
format [r] = formatRange r
format (r : rs) = formatRange r . (',' :) . format rs

solution :: [Integer] -> String
solution myList = format (ranges myList) ""
