{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Coroutine where

import Control.Monad (forever, (>=>))
import Data.Bits (Bits ((.&.)))
import Preloaded

-- Useful alias
apply :: Coroutine r u d a -> (Command r u d a -> r) -> r
apply = runCoroutine

instance Applicative (Coroutine r u d) where
  pure v = Coroutine (\cont -> cont (Done v))
  Coroutine c1 <*> c2 = Coroutine \cont ->
    c1 \case
      Done f -> runCoroutine (f <$> c2) cont
      In iu -> cont (In (\u -> iu u <*> c2))
      Out d c1' -> cont (Out d (c1' <*> c2))

instance Monad (Coroutine r u d) where
  Coroutine cv >>= g = Coroutine \cont ->
    cv \case
      Done r -> runCoroutine (g r) cont
      In iu -> cont (In (iu >=> g))
      Out d cv' -> cont (Out d (cv' >>= g))

(>>>) :: Coroutine r u m a -> Coroutine r m d a -> Coroutine r u d a
c1 >>> Coroutine cf2 = Coroutine \cont ->
  cf2 \case
    Done r -> cont (Done r)
    In im -> runCoroutine (pipe2 c1 im) cont
    Out m p2' -> cont (Out m (c1 >>> p2'))

pipe2 :: Coroutine r u t a -> (t -> Coroutine r t d a) -> Coroutine r u d a
pipe2 (Coroutine c) im = Coroutine \cont ->
  c \case
    Done r -> cont (Done r)
    In iu -> cont (In (\u -> iu u `pipe2` im))
    Out m c1' -> runCoroutine (c1' >>> im m) cont

-- Library functions

output :: a -> Coroutine r u a ()
output v = Coroutine (\cont -> cont (Out v (pure ())))

input :: Coroutine r v d v
input = Coroutine (\cont -> cont (In return))

produce :: [a] -> Coroutine r u a ()
produce [] = pure ()
produce (x : xs) = Coroutine (\cont -> cont (Out x (produce xs)))

consume :: Coroutine [t] u t a -> [t]
consume = reverse . iter []
  where
    iter acc (Coroutine c) =
      c \case
        Done _ -> acc
        In _ -> acc
        Out d c' -> iter (d : acc) c'

filterC :: (v -> Bool) -> Coroutine r v v ()
filterC p =
  Coroutine \cont ->
    cont
      ( In \v ->
          if p v
            then Coroutine (\cont1 -> cont1 (Out v (filterC p)))
            else filterC p
      )

limit :: Int -> Coroutine r v v ()
limit 0 = pure ()
limit n
  | n < 0 = pure ()
  | otherwise = Coroutine \cont ->
      cont (In (\v -> Coroutine (\cont1 -> cont1 (Out v (limit (n - 1))))))

idC :: Coroutine r v v ()
idC = Coroutine \cont ->
  cont (In (\v -> Coroutine (\cont1 -> cont1 (Out v idC))))

suppress :: Int -> Coroutine r v v ()
suppress 0 = idC
suppress n
  | n < 0 = idC
  | otherwise = Coroutine \cont ->
      cont (In (\_ -> suppress (n - 1)))

add :: Coroutine r Int Int ()
add = forever do
  v1 <- input
  v2 <- input
  output (v1 + v2)

duplicate :: Coroutine r v v ()
duplicate = forever do
  v <- input
  output v
  output v

mapC :: (t -> d) -> Coroutine r t d a
mapC f = Coroutine \cont ->
  cont
    ( In \v ->
        Coroutine (\cont1 -> cont1 (Out (f v) (mapC f)))
    )

-- Programs
-- 1. A program which outputs the first 5 even numbers of a stream.
-- 2. A program which produces a stream of the triangle numbers
-- 3. A program which multiplies a stream by 2
-- 4. A program which sums adjacent pairs of integers

p1, p2, p3, p4 :: Coroutine r Int Int ()
p1 = filterC (\v -> v .&. 1 == 0) >>> limit 5
p2 = produce [1 ..] >>> mapC (\v -> v * (v + 1) `div` 2)
p3 = mapC (* 2)
p4 = Coroutine (\cont -> cont (In iter))
  where
    iter lst = Coroutine \cont ->
      cont
        ( In \v ->
            Coroutine (\cont1 -> cont1 (Out (lst + v) (iter v)))
        )
