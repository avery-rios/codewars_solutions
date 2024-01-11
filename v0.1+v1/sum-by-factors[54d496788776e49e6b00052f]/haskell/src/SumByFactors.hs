module Codewars.Kata.SumByFactors (sumOfDivided) where

import Data.Bifunctor
import Data.Foldable
import Data.Int
import Data.IntMap.Strict qualified as IM
import Data.Word

type FacMap = IM.IntMap Int64

divFac :: Word64 -> Word64 -> Word64
divFac n i =
  case n `divMod` i of
    (q, 0) -> divFac q i
    _ -> n

primeFactI :: FacMap -> Int64 -> Word64 -> Word64 -> FacMap
primeFactI fac _ 1 _ = fac
primeFactI fac n v i
  | i > v || i * i > v = IM.insertWith (+) (fromIntegral v) n fac
  | otherwise =
      case v `divMod` i of
        (q, 0) ->
          primeFactI
            (IM.insertWith (+) (fromIntegral i) n fac)
            n
            (divFac v i)
            (i + 1)
        _ -> primeFactI fac n v (i + 1)

sumOfDivided :: [Integer] -> [(Integer, Integer)]
sumOfDivided =
  fmap (bimap fromIntegral fromIntegral)
    . IM.toAscList
    . foldl'
      (\mp i -> primeFactI mp (fromIntegral i) (fromIntegral (abs i)) 2)
      IM.empty
