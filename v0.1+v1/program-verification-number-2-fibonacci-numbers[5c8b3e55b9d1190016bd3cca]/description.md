~~~if:idris
Idris contains a very inefficient implementation of Fibonacci numbers:

```idris
total fib : Nat -> Nat
fib Z         = Z
fib (S Z)     = S Z
fib (S (S n)) = fib (S n) + fib n
```
~~~
~~~if:agda
There's a very inefficient implementation of Fibonacci numbers:

```agda
fib : ℕ -> ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n
```
~~~
~~~if:coq
There's a very inefficient implementation of Fibonacci numbers:

```coq
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n as n') => fib n' + fib n
  end.
```
~~~
~~~if:lean
Here is a very inefficient implementation of Fibonacci numbers:

```lean
def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib (n + 1) + fib n
```
~~~

The preloaded code contains a better implementation:

```idris
module Preloaded

%access public export
%default total

fibAux : Nat -> Nat -> Nat -> Nat
fibAux a b Z = a
fibAux a b (S n) = fibAux b (a + b) n

fib2 : Nat -> Nat
fib2 = fibAux 0 1
```
```agda
{-# OPTIONS --safe #-}
module Preloaded where

fibAux : ℕ -> ℕ -> ℕ -> ℕ
fibAux a b 0 = a
fibAux a b (suc n) = fibAux b (a + b) n

fib2 : ℕ -> ℕ
fib2 = fibAux 0 1
```
```coq
Fixpoint fib_aux (a b n : nat) : nat :=
  match n with
  | 0 => a
  | S n => fib_aux b (a + b) n
  end.
  
Definition fib2 (n : nat) : nat := fib_aux 0 1 n.
```
```lean
def fib_aux : ℕ → ℕ → ℕ → ℕ
| a b 0 := a
| a b (n + 1) := fib_aux b (a + b) n

def fib2 (n : ℕ) : ℕ := fib_aux 0 1 n
```

~~~if:idris
Your task is to prove that `fib2 n = fib n` by implementing the following function:

```idris
fibEq : (n : Nat) -> fib2 n = fib n
fibEq n = ?write_a_proof
```
~~~
~~~if:agda
Your task is to prove that `fib2 n ≡ fib n` by implementing the following function:

```agda
fibEq : (n : ℕ) -> fib2 n ≡ fib n
fibEq n = ?
```
~~~
~~~if:coq
Your task is to prove that 
```coq
forall (n : nat), fib2 n = fib n
```
~~~
~~~if:lean
Your task is to prove that
```
∀ n : ℕ, fib2 n = fib n
```
~~~

## Similar Problems

Please check out the following collections for similar problems:

* [Program Verification](https://www.codewars.com/collections/program-verification-1)
* [Verified Sorting Algorithms](https://www.codewars.com/collections/verified-sorting-algorithms) by [@donaldsebleung](https://www.codewars.com/users/donaldsebleung)  
* [Verified Algorithms](https://www.codewars.com/collections/5d0e575208985f000f6e5671) by [@dramforever](https://www.codewars.com/users/dramforever)