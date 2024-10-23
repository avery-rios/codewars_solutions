{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module InfiniteDigitalString (findPosition) where

import Control.Monad.ST (ST)
import Data.Char (ord)
import Data.Maybe (isJust)
import qualified Data.Vector.Primitive as V
import qualified Data.Vector.Primitive.Mutable as VM
import Data.Word (Word64, Word8)
import qualified Language.Haskell.TH as TH

-- | big endian digits
type Digits = V.Vector Word8

{- number of zero need to remove
    - 010
    - ...
    - 002
    - 001
    - -}
zeroCnt, pow10 :: Word -> Word64
(zeroCnt, pow10) =
  $( let maxPow = 16

         powTableV :: V.Vector Word64
         powTableV = V.unfoldrN (maxPow + 1) (\p -> Just (p, p * 10)) 1

         cntTableV = V.scanl' (+) 0 (V.map (\x -> x - 1) powTableV)

         liftTable :: V.Vector Word64 -> TH.Exp
         liftTable t =
           TH.LamCaseE
             ( zipWith
                 ( \i v ->
                     TH.Match
                       (TH.LitP (TH.IntegerL i))
                       (TH.NormalB (TH.LitE (TH.IntegerL (fromIntegral v))))
                       []
                 )
                 [0 ..]
                 (V.toList t)
             )
      in pure
           ( TH.TupE
               [ Just (liftTable cntTableV),
                 Just (liftTable powTableV)
               ]
           )
   )

numPosition :: Word64 -> Word64
numPosition n =
  let m = n - 1
      lg = log10 0 m
   in m * fromIntegral lg - zeroCnt lg
  where
    log10 :: Word -> Word64 -> Word
    log10 acc 0 = acc
    log10 acc v = log10 (acc + 1) (v `div` 10)

fromDigits :: Digits -> Word64
fromDigits = V.foldl' (\v d -> v * 10 + fromIntegral d) 0

toDigits :: Word64 -> Digits
toDigits w = V.fromList (toList [] w)
  where
    toList acc 0 = acc
    toList acc n =
      let (q, r) = n `divMod` 10
       in toList (fromIntegral r : acc) q

stripPrefix :: V.Vector Word8 -> V.Vector Word8 -> Maybe (V.Vector Word8)
stripPrefix v1 v2 = case V.uncons v1 of
  Just (h1, t1) -> case V.uncons v2 of
    Just (h2, t2) | h1 == h2 -> stripPrefix t1 t2
    _ -> Nothing
  Nothing -> Just v2

stripSuffix :: V.Vector Word8 -> V.Vector Word8 -> Maybe (V.Vector Word8)
stripSuffix v1 v2 = case V.unsnoc v1 of
  Just (i1, l1) -> case V.unsnoc v2 of
    Just (i2, l2) | l1 == l2 -> stripSuffix i1 i2
    _ -> Nothing
  Nothing -> Just v2

checkSuffix :: Word64 -> V.Vector Word8 -> Bool
checkSuffix !w d
  | V.null d = True
  | otherwise =
      let wd = toDigits w
       in if V.length wd <= V.length d
            then case stripPrefix wd d of
              Just suf -> checkSuffix (w + 1) suf
              Nothing -> False
            else isJust (stripPrefix d wd)

-- | try split into suffix(n-1) || n || ... || prefix(n+k)
multiSplit :: V.Vector Word8 -> Int -> Int -> Maybe Word64
multiSplit s start len =
  let (prefix, t1) = V.splitAt start s
      (digits, suffix) = V.splitAt len t1
      w = fromDigits digits
   in if V.head digits /= 0
        && isJust (stripSuffix prefix (toDigits (w - 1)))
        && checkSuffix (w + 1) suffix
        then Just (numPosition w - fromIntegral (V.length prefix))
        else Nothing

iterMultiSplit :: V.Vector Word8 -> Word64 -> Int -> Int -> Word64
iterMultiSplit digits ans len start
  | V.length digits == len =
      min
        ans
        ( if V.head digits /= 0
            then numPosition (fromDigits digits)
            else
              numPosition
                ( fromDigits digits + pow10 (fromIntegral (V.length digits))
                )
                + 1
        )
  | start == len =
      if ans < maxBound -- longer number will occur later
        then ans
        else iterMultiSplit digits ans (len + 1) 0
  | otherwise =
      iterMultiSplit
        digits
        ( case multiSplit digits start len of
            Just p -> min ans p
            Nothing -> ans
        )
        len
        (start + 1)

-- | strip overlap in suffix e.g. (123, 345) -> (123, 45)
stripCommon :: V.Vector Word8 -> V.Vector Word8 -> V.Vector Word8
stripCommon prefix suffix = V.drop (iter 0 0) suffix
  where
    prefixW = fromDigits prefix
    suffixW = fromDigits suffix

    iter ans idx
      | idx >= V.length prefix = ans
      | idx >= V.length suffix = ans
      | otherwise =
          iter
            ( if (prefixW `mod` pow10 (fromIntegral idx))
                == (suffixW `div` pow10 (fromIntegral (V.length suffix - idx)))
                then idx
                else ans
            )
            (idx + 1)

incDigits :: V.Vector Word8 -> V.Vector Word8
incDigits digits =
  V.create
    ( do
        ret <- V.thaw digits
        iter (V.length digits - 1) 1 ret
        pure ret
    )
  where
    iter :: Int -> Word8 -> VM.MVector s Word8 -> ST s ()
    iter 0 c v =
      VM.unsafeModify
        v
        (\d -> let s = d + c in if s > 9 then s - 10 else s)
        0
    iter i c v = do
      d <- VM.unsafeRead v i
      let s = d + c
      if s < 10
        then VM.unsafeWrite v i s
        else do
          VM.unsafeWrite v i (s - 10)
          iter (i - 1) 1 v

-- | split into suffix(n) || prefix(n+1)
singleNum :: V.Vector Word8 -> Int -> Maybe Word64
singleNum digits pos =
  let (preLsb, msb) = V.splitAt pos digits
      lsb = stripCommon msb (incDigits preLsb)
      msbW = fromDigits msb * pow10 (fromIntegral (V.length lsb))
   in if V.head msb == 0
        then Nothing
        else
          Just
            ( numPosition (msbW + fromDigits lsb)
                - fromIntegral (V.length preLsb)
            )

iterSingleNum :: V.Vector Word8 -> Word64 -> Int -> Word64
iterSingleNum digits ans pos
  | pos == V.length digits = ans
  | otherwise =
      iterSingleNum
        digits
        ( case singleNum digits pos of
            Just v -> min ans v
            Nothing -> ans
        )
        (pos + 1)

findPosition :: [Char] -> Integer
findPosition str =
  let digits = V.fromList (fmap (\c -> fromIntegral (ord c - ord '0')) str)
   in fromIntegral
        ( min
            (iterMultiSplit digits maxBound 1 0)
            (iterSingleNum digits maxBound 0)
        )
