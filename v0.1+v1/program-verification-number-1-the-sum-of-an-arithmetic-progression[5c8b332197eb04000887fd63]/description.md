The goal of this kata is to prove that two functions which compute the sum `0 + 1 + 2 + ... + n` are equivalent.

The following code is preloaded:

```idris
module Preloaded

%access public export
%default total

arithSum : Nat -> Nat
arithSum Z = Z
arithSum (S n) = S n + arithSum n

-- We define our own function for dividing a natural
-- number by 2. 
-- The existing Idris function divNatNZ
-- is not a good choice because it is impossible (correct
-- me if I my wrong) to prove many useful properties of
-- divNatNZ.
half : Nat -> Nat
half (S (S n)) = S (half n)
half _ = Z

arithFormula : Nat -> Nat
arithFormula n = half $ n * (n + 1)
```
```agda
{-# OPTIONS --safe #-}
module Preloaded where

open import Data.Nat

arith-sum : ℕ → ℕ
arith-sum zero = zero
arith-sum (suc n) = suc n + arith-sum n

arith-formula : ℕ → ℕ
arith-formula n = ⌊ n * (n + 1) /2⌋
```
```coq
Require Import Arith.

Fixpoint arith_sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => n + arith_sum m
  end.

Definition arith_formula (n : nat) : nat := Nat.div2 (n * (n + 1)).
```
```lean
def arith_sum : ℕ → ℕ
| 0 := 0
| (nat.succ n) := nat.succ n + arith_sum n

def arith_formula (n : ℕ) : ℕ := n * (n + 1) / 2
```
~~~if:idris,agda
Your task is to implement the following function:

```idris
arithEq : (n : Nat) -> arithFormula n = arithSum n
arithEq n = ?write_a_proof
```
```agda
arith-eq : (n : ℕ) -> arith-formula n ≡ arith-sum n
arith-eq n = ?
```
~~~
~~~if:coq,lean
Your task is to prove the following fact:
```coq
forall (n : nat), arith_formula n = arith_sum n
```
```lean
∀ n, arith_formula n = arith_sum n
```
~~~

## Similar Problems

Please check out the following collections for similar problems:

* [Program Verification](https://www.codewars.com/collections/program-verification-1)
* [Verified Sorting Algorithms](https://www.codewars.com/collections/verified-sorting-algorithms) by [@donaldsebleung](https://www.codewars.com/users/donaldsebleung)  
* [Verified Algorithms](https://www.codewars.com/collections/5d0e575208985f000f6e5671) by [@dramforever](https://www.codewars.com/users/dramforever)