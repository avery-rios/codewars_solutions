{-# LANGUAGE Strict #-}

module Become.Immortal (elderAge) where

import Data.Bits
import Data.Int (Int64)
import Data.Word (Word64)

data Range = Range {-# UNPACK #-} Word64 {-# UNPACK #-} Word64

sumMod :: Word64 -> Word64 -> Word64 -> Word64
sumMod start end t =
  let v1 = start + end - 1
      cnt = end - start
   in if testBit cnt 0
        then (((v1 `unsafeShiftR` 1) `mod` t) * (cnt `mod` t)) `mod` t
        else ((v1 `mod` t) * ((cnt `unsafeShiftR` 1) `mod` t)) `mod` t

(.<<!) :: Word64 -> Word64 -> Word64
l .<<! r = unsafeShiftL l (fromIntegral r)

(.>>!) :: Word64 -> Word64 -> Word64
l .>>! r = unsafeShiftR l (fromIntegral r)

mulExp2 :: Word64 -> Word64 -> Word64 -> Word64
mulExp2 l e t = iterMul l e
  where
    pow63 = (1 `unsafeShiftL` 63) `mod` t

    iterMul acc ex
      | ex > 63 = iterMul ((acc * pow63) `mod` t) (ex - 63)
      | otherwise = (acc * ((1 .<<! ex) `mod` t)) `mod` t

sub :: Word64 -> Word64 -> Word64 -> Word64
sub l r t =
  let il = fromIntegral l :: Int64
      ir = fromIntegral r :: Int64
      it = fromIntegral t :: Int64
   in fromIntegral ((il - ir) `mod` it)

xorSum :: Word64 -> Word64 -> Range -> Range -> Word64
xorSum l t r0@(Range _ s0) r1@(Range _ s1) =
  let (Range m lenM, Range n lenN) =
        if s0 > s1
          then (r0, r1)
          else (r1, r0)
      lbLenM = fromIntegral (countTrailingZeros lenM) :: Word64
      lbLenN = fromIntegral (countTrailingZeros lenN) :: Word64
      high = xor m n .&. complement (lenM - 1)
   in if high >= l
        then
          let lbMidCnt = lbLenM - lbLenN
              lbLowCnt = lbLenN + lbLenN

              highSum = mulExp2 (high `mod` t) (lbMidCnt + lbLowCnt) t
              midSum =
                mulExp2
                  (sumMod 0 (1 .<<! lbMidCnt) t)
                  (lbLenN + lbLowCnt)
                  t
              lowSum =
                mulExp2
                  (sumMod 0 (1 .<<! lbLenN) t)
                  (lbLenN + lbMidCnt)
                  t
           in sub
                (highSum + midSum + lowSum)
                (mulExp2 (l `mod` t) (lbMidCnt + lbLowCnt) t)
                t
        else
          if high + lenM > l
            then
              let midGreaterSum =
                    let midMin =
                          ((l .>>! lbLenN) .&. ((1 .<<! (lbLenM - lbLenN)) - 1)) + 1
                        midMax = lenM .>>! lbLenN
                        midCnt = (midMax - midMin) `mod` t

                        lbLowCnt = lbLenN + lbLenN

                        highSum = mulExp2 (((high `mod` t) * midCnt) `mod` t) lbLowCnt t
                        midSum = mulExp2 (sumMod midMin midMax t) (lbLenN + lbLowCnt) t
                        lowSum =
                          ( midCnt
                              * mulExp2
                                (sumMod 0 (1 .<<! lbLenN) t)
                                lbLenN
                                t
                          )
                            `mod` t
                     in sub
                          (highSum + midSum + lowSum)
                          ((midCnt * mulExp2 (l `mod` t) lbLowCnt t) `mod` t)
                          t
                  midEqualSum =
                    let lowMin = l .&. (lenN - 1)
                        lowMax = lenN
                        lowCnt = (lowMax - lowMin) `mod` t

                        middle = (l .>>! lbLenN) .&. ((1 .<<! (lbLenM - lbLenN)) - 1)

                        highMidSum =
                          mulExp2
                            ((((high .|. (middle .<<! lbLenN)) `mod` t) * lowCnt) `mod` t)
                            lbLenN
                            t
                        lowSum = mulExp2 (sumMod lowMin lowMax t) lbLenN t
                     in sub
                          (highMidSum + lowSum)
                          (mulExp2 (((l `mod` t) * lowCnt) `mod` t) lbLenN t)
                          t
               in midGreaterSum + midEqualSum
            else 0

lowbit :: Word64 -> Word64
lowbit b = b .&. (-b)

startRange :: Word64 -> Range
startRange n =
  let ln = lowbit n in Range (n - ln) ln

nextRange :: Range -> Range
nextRange (Range i _) = let li = lowbit i in Range (i - li) li

iter :: Word64 -> Word64 -> Word64 -> Word64 -> Range -> Range -> Word64
iter acc l t _ m@(Range 0 _) i@(Range 0 _) = (acc + xorSum l t m i) `mod` t
iter acc l t n m i@(Range 0 _) =
  iter (acc + xorSum l t m i) l t n (nextRange m) (startRange n)
iter acc l t n m i =
  iter (acc + xorSum l t m i) l t n m (nextRange i)

elderAge :: Integer -> Integer -> Integer -> Integer -> Integer
elderAge 0 _ _ _ = 0
elderAge _ 0 _ _ = 0
elderAge m n l t =
  let wn = fromIntegral n
   in fromIntegral
        ( iter
            0
            (fromIntegral l)
            (fromIntegral t)
            wn
            (startRange (fromIntegral m))
            (startRange wn)
        )
