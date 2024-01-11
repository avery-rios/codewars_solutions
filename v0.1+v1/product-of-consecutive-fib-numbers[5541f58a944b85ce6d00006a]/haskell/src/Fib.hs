module Codewars.Kata.Fib (productFib) where

findProd :: Integer -> Integer -> Integer -> (Integer, Integer, Bool)
findProd p fn fn1 =
  case compare (fn * fn1) p of
    LT -> findProd p fn1 (fn + fn1)
    EQ -> (fn, fn1, True)
    GT -> (fn, fn1, False)

-- | Returns a pair of consecutive Fibonacci numbers a b,
--   where (a*b) is equal to the input, or proofs that the
--   number isn't a product of two consecutive Fibonacci
--   numbers.
productFib :: Integer -> (Integer, Integer, Bool)
productFib n = findProd n 0 1
