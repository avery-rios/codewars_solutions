{-  Do  NOT  remove  -}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -O0 #-}

module Untyped where

data Nat = O | S Nat

-- Uncomment the following line to add your defintion for D
-- In particular, N here is a little primitive type added to
-- our untyped lambda calculus that can be used to witness
-- what goes on behind the scene.
data D = N Nat | Lam (D -> D)

-- app takes an untyped function and an untyped term and calculate
-- the resulting terms after application
app :: D -> D -> D
app (Lam f) v = f v
app _ _ = undefined
{-# NOINLINE app #-}

-- lam takes a function in higher-order abstract syntax (HOAS) and returns
-- an untyped terms representing the function
lam :: (D -> D) -> D
lam = Lam
{-# NOINLINE lam #-}

-- Now let's define church's number
zero :: D
zero =
  lam \_ -> lam \v -> v

suc :: D
suc = lam \n ->
  lam \f -> lam \x ->
    f `app` (n `app` f `app` x)

-- Some other operations we can define
one :: D
one = app suc zero

plus :: D
plus = lam $ \m -> lam $ \n -> m `app` suc `app` n

pair :: D -> D -> D
pair e0 e1 =
  lam \f ->
    f `app` e0 `app` e1

pred :: D
pred = lam \n ->
  n
    `app` lam
      ( \p ->
          app
            p
            ( lam \f -> lam \_ ->
                pair (suc `app` f) f
            )
      )
    `app` pair zero zero
    `app` lam (\_ -> lam \p -> p)

mult :: D
mult = lam \m -> lam \n ->
  m `app` (plus `app` n) `app` zero

-- We can even write out the defintion of y-combinator!
ycomb :: D
ycomb = lam \f ->
  lam (\x -> f `app` (x `app` x)) `app` lam (\x -> f `app` (x `app` x))

-- And true and false
true :: D
true = lam \t -> lam \_ -> t

false :: D
false = lam \_ -> lam \f -> f

-- What about if-then-else?
ite :: D
ite = lam \c -> lam \t -> lam \f ->
  c `app` t `app` f

-- with ite, we can define our lovely
-- logical and/or operators
and :: D
and = lam $ \a -> lam $ \b ->
  ite `app` a `app` b `app` false

or :: D
or = lam $ \a -> lam $ \b ->
  ite `app` a `app` true `app` b

-- Here is the predicate to test if n is zero
iszero :: D
iszero = lam $ \n -> n `app` (lam $ \_ -> false) `app` true

-- This converts the Church encoding to the Peano encoding of natural numbers
toPeano :: D -> D
toPeano (N _) = error "not a Church number!"
toPeano n = n `app` (lam suc_nat) `app` (N O)
  where
    suc_nat (N n) = N (S n)
    suc_nat _ = error "stuck!"

-- This converts the Peano encoding to the Church encoding of natural numbers
fromPeano :: D -> D
fromPeano (N O) = zero
fromPeano (N (S n)) = app suc (fromPeano (N n))
fromPeano _ = error "not a Peano number!"

showPeano :: D -> Int
showPeano (N n) = iterN 0 n
  where
    iterN acc O = acc
    iterN acc (S s) = iterN (acc + 1) s
showPeano _ = undefined
