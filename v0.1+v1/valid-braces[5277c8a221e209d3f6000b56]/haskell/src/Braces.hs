module Codewars.Kata.Braces (validBraces) where

bracesIter :: [Char] -> String -> Bool
bracesIter [] [] = True
bracesIter ('}' : ct) ('}' : xs) = bracesIter ct xs
bracesIter (']' : ct) (']' : xs) = bracesIter ct xs
bracesIter (')' : ct) (')' : xs) = bracesIter ct xs
bracesIter cs ('[' : xs) = bracesIter (']' : cs) xs
bracesIter cs ('(' : xs) = bracesIter (')' : cs) xs
bracesIter cs ('{' : xs) = bracesIter ('}' : cs) xs
bracesIter _ _ = False

validBraces :: String -> Bool
validBraces = bracesIter []
