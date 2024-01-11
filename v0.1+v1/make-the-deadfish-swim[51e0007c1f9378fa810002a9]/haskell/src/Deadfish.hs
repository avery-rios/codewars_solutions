module Kata.Deadfish (parse) where

eval :: Int -> [Int] -> String -> [Int]
eval _ !arr [] = arr
eval n !arr (x : xs) = case x of
  'i' -> eval (n + 1) arr xs
  'd' -> eval (n - 1) arr xs
  's' -> eval (n * n) arr xs
  'o' -> eval n (n : arr) xs
  _ -> eval n arr xs

parse :: String -> [Int]
parse = reverse . eval 0 []
