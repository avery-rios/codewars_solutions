{-# LANGUAGE LambdaCase #-}

module TopWords (top3) where

import Data.Char
import Data.Foldable
import Data.HashMap.Strict qualified as M
import Data.Text qualified as T

type WordMap = M.HashMap T.Text Int

data WordOcc = WordOcc !T.Text {-# UNPACK #-} !Int

emptyWordOcc :: WordOcc
emptyWordOcc = WordOcc T.empty 0

data Top3 = Top3 !WordOcc !WordOcc !WordOcc

addTop3 :: Top3 -> T.Text -> Int -> Top3
addTop3 ws@(Top3 w1@(WordOcc _ o1) w2@(WordOcc _ o2) (WordOcc _ o3)) t o
  | o >= o1 = Top3 (WordOcc t o) w1 w2
  | o >= o2 = Top3 w1 (WordOcc t o) w2
  | o >= o3 = Top3 w1 w2 (WordOcc t o)
  | otherwise = ws

toStrList :: Top3 -> [String]
toStrList (Top3 (WordOcc _ 0) _ _) = []
toStrList (Top3 (WordOcc s _) w2 w3) =
  T.unpack s
    : case w2 of
      WordOcc _ 0 -> []
      WordOcc s2 _ ->
        T.unpack s2 : case w3 of
          WordOcc _ 0 -> []
          WordOcc s3 _ -> [T.unpack s3]

top3 :: [Char] -> [[Char]]
top3 =
  toStrList
    . M.foldlWithKey' addTop3 (Top3 emptyWordOcc emptyWordOcc emptyWordOcc)
    . foldl' (\m w -> M.insertWith (+) w 1 m) M.empty
    . filter (T.any isAlpha)
    . T.words
    . T.map
      ( \case
          '\'' -> '\''
          c
            | isAlpha c -> toLower c
            | otherwise -> ' '
      )
    . T.pack
