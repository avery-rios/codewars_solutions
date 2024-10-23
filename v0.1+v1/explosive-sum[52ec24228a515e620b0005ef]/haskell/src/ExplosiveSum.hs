{-# LANGUAGE Strict #-}

module ExplosiveSum (explosiveSum) where

import Control.Monad.ST (ST)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM

matIndex :: Word -> Word -> Word -> Int
matIndex n num maxVal = fromIntegral (num * (n + 1) + maxVal)

fill :: Int -> Int -> Integer -> VM.MVector s Integer -> ST s ()
fill _ 0 _ _ = pure ()
fill start len val mat =
  VM.unsafeWrite mat start val >> fill (start + 1) (len - 1) val mat

sumRow :: Word -> Word -> Word -> Integer -> VM.MVector s Integer -> ST s Integer
sumRow n num maxVal lst mat = do
  cnt <- VM.unsafeRead mat (matIndex n (num - maxVal) maxVal)
  let cur = cnt + lst
  VM.unsafeWrite mat (matIndex n num maxVal) cur
  if maxVal /= num
    then sumRow n num (maxVal + 1) cur mat
    else pure cur

sumIter :: Word -> Word -> VM.MVector s Integer -> ST s ()
sumIter n num mat = do
  v <- sumRow n num 1 0 mat
  if n == num
    then pure ()
    else do
      -- when maxVal > num, mat[num,maxVal] = mat[num,num]
      fill (matIndex n num (num + 1)) (fromIntegral (n - num)) v mat
      sumIter n (num + 1) mat

createMat :: Word -> V.Vector Integer
createMat n =
  V.create
    ( do
        -- mat[i,j] partition of i using number less or equal than j
        mat <- VM.replicate (fromIntegral ((n + 1) * (n + 1))) 0
        -- mat[0,i] = 1
        fill 0 (fromIntegral (n + 1)) 1 mat
        sumIter n 1 mat
        pure mat
    )

explosiveSum :: Integer -> Integer
explosiveSum n =
  let wn = fromIntegral n :: Word
   in V.unsafeIndex (createMat wn) (matIndex wn wn wn)
