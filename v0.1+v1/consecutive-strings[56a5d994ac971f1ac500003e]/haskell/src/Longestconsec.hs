module Codewars.G964.Longestconsec (longestConsec) where

import Data.List qualified as L

longestPosI :: Int -> Int -> Int -> Int -> [Int] -> [Int] -> Int
longestPosI pos _ _ _ _ [] = pos
longestPosI pos posCnt idx lastCnt (f : fs) (x : xs) =
  let curCnt = lastCnt + x
   in if curCnt > posCnt
        then longestPosI idx curCnt (idx + 1) (curCnt - f) fs xs
        else longestPosI pos posCnt (idx + 1) (curCnt - f) fs xs

longestConsec :: [String] -> Int -> String
longestConsec strarr k
  | k <= 0 = ""
  | length strarr < k = ""
  | otherwise =
      let lens = fmap length strarr
          (fl, ol) = L.splitAt (k - 1) lens
          lPos = longestPosI 0 0 0 (sum fl) lens ol
       in concat (L.take k (L.drop lPos strarr))
