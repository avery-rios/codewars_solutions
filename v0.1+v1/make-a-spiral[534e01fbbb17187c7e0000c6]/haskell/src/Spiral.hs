module Spiral (spiralize) where

import Data.Foldable (foldl')

addRevPrefix :: [Int] -> [Int] -> [Int]
addRevPrefix ps l = foldl' (flip (:)) l ps

addReplicate :: Int -> Int -> [Int] -> [Int]
addReplicate 0 _ l = l
addReplicate n v l = addReplicate (n - 1) v (v : l)

repRow :: Int -> Int -> [Int] -> [Int] -> [Int]
repRow n v pref suff = addRevPrefix pref (addReplicate n v suff)

spirRow :: [Int] -> [Int] -> Int -> Int -> [Int]
spirRow pref suff 1 _ = addRevPrefix pref (1 : suff)
spirRow pref suff 2 l =
  addRevPrefix
    pref
    ( case l of
        0 -> 1 : 1 : suff
        1 -> 0 : 1 : suff
        _ -> error "Invalid row"
    )
spirRow pref suff 3 l =
  addRevPrefix
    pref
    ( case l of
        0 -> 1 : 1 : 1 : suff
        1 -> 0 : 0 : 1 : suff
        2 -> 1 : 1 : 1 : suff
        _ -> error "Invalid row"
    )
spirRow pref suff 4 l =
  addRevPrefix
    pref
    ( case l of
        0 -> 1 : 1 : 1 : 1 : suff
        1 -> 0 : 0 : 0 : 1 : suff
        2 -> 1 : 0 : 0 : 1 : suff
        3 -> 1 : 1 : 1 : 1 : suff
        _ -> error "Invalid row"
    )
spirRow pref suff n 0 = repRow n 1 pref suff
spirRow pref suff n 1 = repRow (n - 1) 0 pref (1 : suff)
spirRow pref suff n 2 = repRow (n - 2) 1 pref (0 : 1 : suff)
spirRow pref suff n l
  | l == n - 1 = repRow n 1 pref suff
  | l == n - 2 = repRow (n - 2) 0 (1 : pref) (1 : suff)
  | otherwise = spirRow (0 : 1 : pref) (0 : 1 : suff) (n - 4) (l - 2)

spiralize :: Int -> [[Int]]
spiralize n = fmap (spirRow [] [] n) [0 .. n - 1]
