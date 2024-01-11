module Codewars.G964.WeightSort (orderWeight) where

import Data.Char
import Data.List qualified as L

orderWeight :: [Char] -> [Char]
orderWeight =
  L.unwords
    . fmap snd
    . L.sort
    . fmap (\w -> (sum (fmap digitToInt w), w))
    . L.words
