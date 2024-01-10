module Codewars.G964.Scramblies (scramble) where

import Data.Char (ord)
import Data.Foldable
import Data.IntMap.Strict qualified as IM

type CharMap = IM.IntMap Int

charMap :: [Char] -> CharMap
charMap =
  foldl'
    (\mp c -> IM.insertWith (+) (ord c - ord 'a') 1 mp)
    IM.empty

scramble :: [Char] -> [Char] -> Bool
scramble s1 s2 = IM.isSubmapOfBy (<=) (charMap s2) (charMap s1)
