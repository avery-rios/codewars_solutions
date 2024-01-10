module SortArray (sortArray) where

import Data.List qualified as L

mergeOdd :: [Int] -> [Int] -> [Int] -> [Int]
mergeOdd _ _ [] = []
mergeOdd es os (x : xs)
  | even x = head es : mergeOdd (tail es) os xs
  | otherwise = head os : mergeOdd es (tail os) xs

sortArray :: [Int] -> [Int]
sortArray xs =
  let (es, os) = L.partition even xs
   in mergeOdd es (L.sort os) xs
