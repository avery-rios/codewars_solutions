{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RebindableSyntax #-}

module ImperativeSpec where

import Imperative (def, elif', else', if', push, return, toString, var, while, (*=), (+=), (-=), (.=), (>>), (>>=))
import Preloaded (isDivisibleBy)
import Test.Hspec
import Test.QuickCheck
import Prelude hiding (return, (>>), (>>=))
import qualified Prelude as P

spec :: Spec
spec = do
  describe "def" do
    it "def should be the inverse of var" do
      property $ \x -> def (var x) `shouldBe` (x :: Integer)
  describe "programs should return the same as their functional counterparts" do
    it "factorial" do
      property $ \x -> factorial x `shouldBe` product [1 .. x]
    it "sumFromTo" do
      property $ \from to ->
        sumFromTo from to `shouldBe` sum [from .. to]
    it "howManyBetween" do
      property $ \from to ->
        howManyBetween from to `shouldBe` max 0 (to - from - 1)
    it "fizzBuzz" do
      property $ \from to ->
        fizzBuzz from to `shouldBe` fizzBuzzFunctional from to
    it "isEven" do
      property $ \integer ->
        isEven integer `shouldBe` even integer
  where
    a >> b = a P.>> b

factorial :: Integer -> Integer
factorial n = def do
  result <- var 1
  i <- var n
  while i (>) 0 do
    result *= i
    i -= 1
  return result

sumFromTo :: Integer -> Integer -> Integer
sumFromTo c n = def do
  result <- var 0
  i <- var c
  while i (<=) n do
    result += i
    i += 1
  return result

howManyBetween :: Integer -> Integer -> Integer
howManyBetween c n = def do
  result <- var 0
  i <- var (c + 1)
  while i (<) n do
    result += 1
    i += 1
  return result

fizzBuzz :: Integer -> Integer -> [String]
fizzBuzz from to = def do
  result <- var []
  current <- var from

  while current (<=) to do
    if' current isDivisibleBy 15 do
      result `push` "FizzBuzz"

    elif' current isDivisibleBy 3 do
      result `push` "Fizz"

    elif' current isDivisibleBy 5 do
      result `push` "Buzz"

    else' do
      currentAsString <- toString current
      result `push` currentAsString

    current += 1

  return result

fizz :: Integer -> String
fizz n
  | n `mod` 15 == 0 = "FizzBuzz"
  | n `mod` 3 == 0 = "Fizz"
  | n `mod` 5 == 0 = "Buzz"
  | otherwise = show n

fizzBuzzFunctional :: Integer -> Integer -> [String]
fizzBuzzFunctional from to = fizz <$> [from .. to]

isEven :: Integer -> Bool
isEven int = def do
  result <- var False
  if' int isDivisibleBy 2 do
    result .= True
  return result
