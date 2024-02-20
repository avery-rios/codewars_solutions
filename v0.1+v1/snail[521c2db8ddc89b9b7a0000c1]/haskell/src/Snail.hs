module Snail (snail) where

import qualified Data.List as L
import qualified Data.Vector as V
import Data.Vector.Generic
import qualified Data.Vector.Unboxed as UV

type Matrix = V.Vector (UV.Vector Int)

{- UUUUR
 - L   R
 - L   R
 - LDDDD
 - U : upper
 - R: right
 - L: left
 - D: down
 - -}

snailF :: Matrix -> [Int] -> Word -> Int -> [Int]
snailF _ acc 0 _ = acc
snailF mat acc 1 off = (mat ! off ! off) : acc
snailF mat acc n off =
  let ni = fromIntegral n - 1
      siz = V.length mat
      upper = foldl' (flip (:)) acc (slice off ni (mat ! off))
      right =
        let pos = siz - off - 1
         in foldl' (\a v -> (v ! pos) : a) upper (slice off ni mat)
      lower = foldr' (:) right (slice (off + 1) ni (mat ! (siz - off - 1)))
      left = foldr' (\v a -> (v ! off) : a) lower (slice (off + 1) ni mat)
   in snailF mat left (n - 2) (off + 1)

snail :: [[Int]] -> [Int]
snail [] = []
snail [[]] = []
snail v =
  let mat = V.fromList (fmap UV.fromList v)
   in L.reverse (snailF mat [] (fromIntegral (V.length mat)) 0)
