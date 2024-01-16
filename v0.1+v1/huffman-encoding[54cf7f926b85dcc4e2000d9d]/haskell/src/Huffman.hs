{-# LANGUAGE Strict #-}

module Huffman
  ( frequencies,
    encode,
    decode,
    Bit (..),
  )
where

import Data.List (foldl', sort)
import qualified Data.Map.Strict as M

data Bit = Z | O deriving (Eq, Show)

-- | Calculate symbol frequencies of a text.
frequencies :: (Ord a) => [a] -> [(a, Int)]
frequencies = M.toList . foldl' (\mp i -> M.insertWith (+) i 1 mp) M.empty

-- | key for map
-- MapKey freq index
-- add index to distinguish different element with same freq
data MapKey = MapKey Int Int
  deriving (Eq, Ord)

data Tree a
  = Leaf a
  | Branch (Tree a) (Tree a)

buildTreeI :: M.Map MapKey (Tree a) -> Tree a
buildTreeI m =
  case M.size m of
    1 -> head (M.elems m)
    2 ->
      let [h, t] = M.elems m
       in Branch h t
    _ ->
      let ((MapKey c1 k1, t1), m1) = M.deleteFindMin m
          ((MapKey c2 _, t2), m2) = M.deleteFindMin m1
       in buildTreeI (M.insert (MapKey (c1 + c2) k1) (Branch t1 t2) m2)

buildTree :: (Ord a) => [(a, Int)] -> Tree a
buildTree fs =
  buildTreeI
    ( snd
        ( foldl'
            (\(idx, mp) (v, f) -> (idx + 1, M.insert (MapKey f idx) (Leaf v) mp))
            (0, M.empty)
            (sort fs)
        )
    )

letterCodeI :: (Ord a) => M.Map a [Bit] -> [Bit] -> Tree a -> M.Map a [Bit]
letterCodeI mp path (Leaf a) = M.insert a (reverse path) mp
letterCodeI mp path (Branch l r) =
  let codeL = letterCodeI mp (Z : path) l
   in letterCodeI codeL (O : path) r

letterCode :: (Ord a) => Tree a -> M.Map a [Bit]
letterCode = letterCodeI M.empty []

-- | Encode a sequence using the given frequencies.
encode :: (Ord a) => [(a, Int)] -> [a] -> Maybe [Bit]
encode [] _ = Nothing
encode [_] _ = Nothing
encode freq ls =
  let codes = letterCode (buildTree freq)
   in concat <$> traverse (`M.lookup` codes) ls

decodeOne :: Tree a -> [Bit] -> Maybe (a, [Bit])
decodeOne (Leaf a) bs = Just (a, bs)
decodeOne (Branch _ _) [] = Nothing
decodeOne (Branch l r) (b : bs) =
  decodeOne
    ( case b of
        Z -> l
        O -> r
    )
    bs

getLettersI :: Tree a -> [Bit] -> Maybe [a]
getLettersI _ [] = Just []
getLettersI root bs =
  decodeOne root bs >>= \(v, r) ->
    (v :) <$> getLettersI root r

-- | Decode a bit sequence using the given frequencies.
decode :: (Ord a) => [(a, Int)] -> [Bit] -> Maybe [a]
decode [] _ = Nothing
decode [_] _ = Nothing
decode freq bs = getLettersI (buildTree freq) bs
