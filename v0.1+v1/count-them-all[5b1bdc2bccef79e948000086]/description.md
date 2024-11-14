Every type `a :: *` can be mapped to `Nat`ural number of its inhabitants (possibly zero or infinite). In this kata we'll develop this mapping with `Count` for some common types.
```haskell
data Nat = Z | S Nat deriving (Show, Eq, Ord)
newtype Count (a :: *) = Count { getCount :: Nat } deriving (Show, Eq, Ord)
```
There are some useful functions for working with `Count` (you are free to delete/rename/ignore them, they won't be tested):
```haskell
mapC :: (Nat -> Nat) -> Count a -> Count b
liftC2 :: (Nat -> Nat -> Nat) -> Count a -> Count b -> Count c
coerceC :: Count a -> Count b
```
To create _"function"_ &nbsp;from a type to `Nat` we'll use typeclass:
```haskell
class Countable c where
  count :: Count c
  -- count' :: Proxy c -> Count c -- optional, you may use TypeApplication
```
You are free to use
- **[Proxy](http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Proxy.html)**: `data Proxy (a :: k) = Proxy`. Then implement `count'` from `count` and vice versa (same with `factor` and `list`). Now you could use `count'`, `factor'`, `list'` in instances:

  ```count' (Proxy :: Proxy Bool) `shouldBe` Count 2```
- **[Type Application](https://ghc.haskell.org/trac/ghc/wiki/TypeApplication)**: add pragma `{-# LANGUAGE TypeApplications #-}` to the top and ignore/remove `count'`, `factor'`, `list'`. Usage:

  ```count @Bool `shouldBe` Count 2```


Your first task is to provide `Countable` instances:
```haskell
instance Countable Void
instance Countable ()
instance Countable Bool
instance Countable Nat
```
<br>

As well as type of kind `*` could be mapped to `Nat`, type of kind `* -> *` could be mapped to `Nat -> Nat`, we'll do it with additional typeclass:
```haskell
class Factor (f :: * -> *) where
  factor :: Count c -> Count (f c)
  -- factor' :: Proxy f -> Count c -> Count (f c)

instance (Factor f, Countable c) => Countable (f c) where
  count = error "of course it is not useless"
```
Your second task is to provide following instances of `Factor`:
```haskell
instance Factor Maybe
instance Factor Identity
instance Factor Proxy
instance Factor Count
instance Factor []
instance Countable c => Factor (Const c)
instance Countable c => Factor (Either c)
instance Countable c => Factor ((,) c)
instance Countable c => Factor ((->) c)
instance (Factor f, Factor g) => Factor (Sum f g)
instance (Factor f, Factor g) => Factor (Product f g)
instance (Factor f, Factor g) => Factor (Compose f g)
```
NOTE:
```haskell
newtype Identity a = Identity {runIdentity :: a}
newtype Const a b = Const {getConst :: a}
data Sum f g a = InL (f a) | InR (g a)
data Product f g a = Pair (f a) (g a)
newtype Compose f g a = Compose {getCompose :: f (g a)}
```
<br>

Your last task is to prove that you understand what on earth are you counting by providing following instances of `Listable`:
```haskell
class Countable a => Listable a where
  list :: [a] -- list of all inhabitants
  -- list' :: Proxy a -> [a]
-- | genericLength (list :: [a]) `shouldBe` getCount (count :: Count a)

instance Listable Void
instance Listable ()
instance Listable Bool
instance Listable Nat

instance Listable c => Listable (Maybe c)
instance Listable c => Listable [c]
instance (Listable a, Listable b) => Listable (Either a b)
instance (Listable a, Listable b) => Listable (a, b)
instance (Eq a, Listable a, Listable b) => Listable (a -> b)
```
Order of inhabitants in infinite lists won't be tested.
<br>

P. S. If you liked counting then you could count some natural transformations in [Yoneda Lemma](https://www.codewars.com/kata/yoneda-lemma).
<br>
<br>

P. P. S. `Preloaded` module for local testing:
```haskell
module Counting.Preloaded where
import Control.Arrow ((***))

data Nat = Z | S Nat deriving (Show, Eq, Ord)

nat :: a -> (Nat -> a) -> Nat -> a
nat a _ Z = a
nat _ aa (S n) = aa n

iterNat :: (a -> a) -> Nat -> (a -> a)
iterNat _ Z = id
iterNat aa (S n) = aa . iterNat aa n

natUnderflow :: String
natUnderflow = "Nat is non-negative"

instance Num Nat where
  (+) = iterNat S
  a * b = iterNat (b+) a Z
  a - Z = a
  Z - b = error natUnderflow
  S a - S b = a - b
  abs = id
  signum Z = Z
  signum (S _) = S Z
  fromInteger x
    | x < 0 = error natUnderflow
    | x == 0 = Z
    | otherwise = S $ fromInteger $ x - 1

instance Enum Nat where
  toEnum x
    | x < 0 = error natUnderflow
    | x == 0 = Z
    | otherwise = S $ toEnum $ x - 1
  fromEnum x = iterNat (+1) x 0

instance Real Nat where toRational = toRational . fromEnum

instance Integral Nat where
  quotRem a Z = error "divide by zero"
  quotRem a b = until ((< b) . snd) (S *** subtract b) (Z, a)
  divMod = quotRem
  toInteger n = iterNat (+1) n 0
```