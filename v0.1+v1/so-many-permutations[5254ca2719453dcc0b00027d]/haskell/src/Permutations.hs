module Codewars.Kata.Permutations (permutations) where

import Data.Foldable
import Data.List (sort)

spanEq :: Char -> String -> String -> (String, String)
spanEq _ pre [] = (pre, [])
spanEq c pre (x : xs)
  | x == c = spanEq c (x : pre) xs
  | otherwise = (pre, x : xs)

addRevPrefix :: String -> String -> String
addRevPrefix pre s = foldl' (flip (:)) s pre

permuI :: [String] -> String -> String -> [String]
permuI ans _ [] = ans
permuI ans pre (x : xs) =
  let perm = permuSorted (addRevPrefix pre xs) -- permutation without x
      (as, other) = spanEq x pre xs -- move duplicate elem in xs to pre
   in permuI
        ( foldl'
            (\acc p -> (x : p) : acc)
            ans
            perm
        )
        (x : as)
        other

permuSorted :: String -> [String]
permuSorted [] = [[]]
permuSorted xs = permuI [] [] xs

permutations :: String -> [String]
permutations = permuSorted . sort
