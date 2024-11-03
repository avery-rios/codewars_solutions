{-# LANGUAGE Strict #-}

module Faberge (height) where

import Data.Bits
import qualified Data.Vector.Primitive as PV
import Data.Word (Word64)

maxN :: Int
maxN = 80000

mo :: Word64
mo = 998244353

inv :: Word64 -> Word64
inv v = iter 1 v (mo - 2)
  where
    iter acc _ 0 = acc
    iter acc p i =
      iter
        (if testBit i 0 then (acc * p) `mod` mo else acc)
        ((p * p) `mod` mo)
        (i `unsafeShiftR` 1)

prev :: Word64 -> Word64
prev 0 = mo - 1
prev n = n - 1

factor :: Word64 -> Word64
factor = iter 1
  where
    iter acc 0 = acc
    iter acc n = iter ((acc * n) `mod` mo) (n - 1)

invFactorTable :: PV.Vector Word64
invFactorTable =
  PV.reverse
    ( PV.unfoldrExactN
        (maxN + 1)
        (\(iPrd, i) -> (iPrd, ((iPrd * i) `mod` mo, i - 1)))
        (inv (factor (fromIntegral maxN)), fromIntegral maxN)
    )

-- |
--    Let height1 n m be max number of floor, then
--
--    >   height1 _ 0 = 1
--    >   height1 0 _ = 1
--    >   height1 n m = height1 (n-1) (m-1) + height1 (n-1) m
--
--
--    Generative function: \(\frac{1}{1-x}(x+1)^m = (x+1)^m\frac{1}{1-x}\),
--    which is \(\sum_{i=0}^{n}\binom{i}{m}\)
--
--    Since \(\binom{0}{m} = 0\) and @height n m = height1 n m - 1@,
--    @height n m@ is \(\sum_{i=1}^{n}\binom{i}{m}\)
height :: Integer -> Integer -> Integer
height _ 0 = 0
height 0 _ = 0
height n m =
  let vm = fromIntegral (m `mod` fromIntegral mo)
   in fromIntegral (iter 0 vm vm vn)
  where
    vn = fromIntegral (min n m)

    -- sum of C(i,m), i in 1..n, i = (n+1) - ni
    iter :: Word64 -> Word64 -> Word64 -> Int -> Word64
    iter acc _ _ 0 = acc
    iter acc perm mi ni =
      let nextM = prev mi
          iFac = PV.unsafeIndex invFactorTable (vn + 1 - ni)
       in iter
            ((acc + perm * iFac) `mod` mo)
            ((perm * nextM) `mod` mo)
            nextM
            (ni - 1)
