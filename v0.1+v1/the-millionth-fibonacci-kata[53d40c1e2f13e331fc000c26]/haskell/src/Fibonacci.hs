{-# LANGUAGE Strict #-}

module Fibonacci (fib) where

import Data.Bits

data Vect = Vect Integer Integer

data Matrix = Matrix {-# UNPACK #-} Vect {-# UNPACK #-} Vect

mvMul :: Matrix -> Vect -> Vect
mvMul (Matrix (Vect l00 l10) (Vect l01 l11)) (Vect r0 r1) =
  Vect (r0 * l00 + r1 * l01) (r0 * l10 + r1 * l11)
{-# INLINE mvMul #-}

mMul :: Matrix -> Matrix -> Matrix
mMul lm (Matrix r0 r1) = Matrix (mvMul lm r0) (mvMul lm r1)
{-# INLINE mMul #-}

mPow :: Matrix -> Int -> Matrix
mPow m = f m (Matrix (Vect 1 0) (Vect 0 1))
  where
    f :: Matrix -> Matrix -> Int -> Matrix
    f _ acc 0 = acc
    f pw acc n =
      f
        (mMul pw pw)
        (if n .&. 1 == 1 then mMul acc pw else acc)
        (n `unsafeShiftR` 1)

fibPos :: Int -> Integer
fibPos n =
  let Vect r _ = mPow (Matrix (Vect 0 1) (Vect 1 1)) n `mvMul` Vect 0 1
   in r

fibNeg :: Int -> Integer
fibNeg n =
  let Vect r _ = mPow (Matrix (Vect (-1) 1) (Vect 1 0)) (-n) `mvMul` Vect 0 1
   in r

fib :: Integer -> Integer
fib n
  | n >= 0 = fibPos (fromIntegral n)
  | otherwise = fibNeg (fromIntegral n)
