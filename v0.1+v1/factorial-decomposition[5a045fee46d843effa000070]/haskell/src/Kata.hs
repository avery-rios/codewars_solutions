{-# LANGUAGE BlockArguments #-}

module FactorialDecomposition.Kata (decomp) where

import Control.Monad (when)
import Data.Array.ST
import Data.Array.Unboxed
import Data.Foldable (for_)

facCount :: Int -> Int -> Int -> Int
facCount acc _ 0 = acc
facCount acc k n =
  let v = n `div` k
   in facCount (acc + v) k v

primes :: Int -> UArray Int Bool
primes n = runSTUArray do
  arr <- newArray (2, n) True
  for_ [2 .. n] \i -> do
    isP <- readArray arr i
    when isP do
      for_ [i + i, i + i + i .. n] \j -> do
        writeArray arr j False
  pure arr

toStr :: String -> Int -> Int -> UArray Int Bool -> String
toStr acc n 1 _ = acc
toStr acc n x arr =
  toStr
    ( if arr ! x
        then
          ( case facCount 0 x n of
              1 -> shows x
              cnt -> shows x . ("^" ++) . shows cnt
          )
            ( case acc of
                [] -> []
                as -> ' ' : '*' : ' ' : as
            )
        else acc
    )
    n
    (x - 1)
    arr

decomp :: Int -> String
decomp n = toStr "" n n (primes n)
