module Codewars.Kata.Dioph (solequa) where

import Data.Foldable

solve :: [(Integer, Integer)] -> Int -> Int -> [(Integer, Integer)]
solve !ans n fac1
  | fac1 * fac1 > n = ans
  | (fac2, 0) <- n `divMod` fac1,
    (x, 0) <- (fac1 + fac2) `divMod` 2,
    (y, 0) <- (fac2 - fac1) `divMod` 4 =
      solve
        ((fromIntegral x, fromIntegral y) : ans)
        n
        (fac1 + 1)
  | otherwise = solve ans n (fac1 + 1)

solequa :: Integer -> [(Integer, Integer)]
solequa n = reverse (solve [] (fromIntegral n) 1)
