{-# LANGUAGE BangPatterns #-}

module MTF (encode, decode) where

import Data.Foldable (Foldable (foldl'))

-- | add reverse prefix and cons current head
addPrefix :: a -> [a] -> [a] -> [a]
addPrefix x xs l = x : foldl' (flip (:)) l xs

getIndexI :: (Eq a) => Int -> [a] -> a -> [a] -> Maybe (Int, [a])
getIndexI _ _ _ [] = Nothing
getIndexI n !pref a (x : xs)
  | a == x = Just (n, addPrefix x pref xs)
  | otherwise = getIndexI (n + 1) (x : pref) a xs

-- | get index and shift
getIndex :: (Eq a) => a -> [a] -> Maybe (Int, [a])
getIndex = getIndexI 0 []

-- | Encode a sequence using the Move-To-Front encoding.
encode :: (Eq a) => [a] -> [a] -> Maybe [Int]
encode _ [] = Just []
encode alpha (x : xs) = do
  (idx, alpha') <- getIndex x alpha
  ts <- encode alpha' xs
  pure (idx : ts)

getItemI :: [a] -> Int -> [a] -> Maybe (a, [a])
getItemI _ _ [] = Nothing
getItemI pref 0 (x : xs) = Just (x, addPrefix x pref xs)
getItemI pref n (x : xs) = getItemI (x : pref) (n - 1) xs

getItem :: Int -> [a] -> Maybe (a, [a])
getItem = getItemI []

-- | Decode alphabet indices from the Move-To-Front encoding.
decode :: (Eq a) => [a] -> [Int] -> Maybe [a]
decode _ [] = Just []
decode alpha (x : xs) = do
  (v, alpha') <- getItem x alpha
  vs <- decode alpha' xs
  pure (v : vs)
