{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

module AlphabeticAnagrams (lexiPos) where

import Data.Array.IArray
import Data.Char (ord)
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L

type FacTab = Array Int Integer

facTab :: Int -> FacTab
facTab n = array (0, n) (facI [(0, 1)] 1 1)
  where
    facI :: [(Int, Integer)] -> Integer -> Int -> [(Int, Integer)]
    facI lst acc i =
      let cur = acc * fromIntegral i
          cLst = (i, cur) : lst
       in if i == n
            then cLst
            else facI cLst cur (i + 1)

type CharMap = IM.IntMap Int

removeChar :: Int -> CharMap -> CharMap
removeChar =
  IM.update
    ( \case
        1 -> Nothing
        cnt -> Just (cnt - 1)
    )

-- | permutation count of chars begin with chars less then upper
permu :: FacTab -> Int -> CharMap -> Int -> Integer
permu fac len cm upper =
  let (lt, gt) = IM.split upper cm
      upperPermu =
        IM.foldl'
          (\acc cnt -> acc `div` (fac ! cnt))
          ( case IM.lookup upper cm of
              Just cnt -> (fac ! (len - 1)) `div` (fac ! cnt)
              Nothing -> error "Invalid map"
          )
          gt
      ascLst = IM.toAscList lt
      ascCnt = fmap snd ascLst
   in sum
        ( zipWith3
            (\p s (_, i) -> upperPermu `div` (p * s * (fac ! (i - 1))))
            (snd (L.mapAccumL (\acc i -> (acc * (fac ! i), acc)) 1 ascCnt))
            (snd (L.mapAccumR (\acc i -> (acc * (fac ! i), acc)) 1 ascCnt))
            ascLst
        )

lexiI :: FacTab -> Int -> CharMap -> Integer -> String -> Integer
lexiI _ _ _ acc [] = acc
lexiI fac len cm acc ('A' : xs) =
  lexiI
    fac
    (len - 1)
    (removeChar (ord 'A') cm)
    acc
    xs
lexiI fac len cm acc (x : xs) =
  let idx = ord x
   in lexiI
        fac
        (len - 1)
        (removeChar idx cm)
        (acc + permu fac len cm idx)
        xs

lexiPos :: String -> Integer
lexiPos s =
  let charMap = L.foldl' (\cm i -> IM.insertWith (+) (ord i) 1 cm) IM.empty s
      len = length s
   in 1 + lexiI (facTab len) len charMap 0 s
