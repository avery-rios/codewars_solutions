_This Kata is a part of a collection of [supplementary exercises for Logical Foundations](https://www.codewars.com/collections/supplementary-exercises-for-logical-foundations)._

Consider the set of all natural numbers that are multiples of 3.  A straightforward inductive definition of this set is as follows:

- 0 is a multiple of 3
- For every natural number n that is a multiple of 3, 3 + n is also a multiple of 3

Another possible but rather clumsy inductive definition of the same set is as follows:

- 30 is a multiple of 3
- 21 is a multiple of 3
- For every pair of natural numbers (n, m) that are both multiples of 3, n + m is also a multiple of 3
- For every ordered triple of natural numbers (l, n, m) where n, m are multiples of 3 and l + n = m, l is also a multiple of 3

Prove that both inductive definitions do indeed define the same set.

~~~if:coq
### Preloaded.v

```coq
Inductive multiple_of_3 : nat -> Prop :=
  | O_multiple : multiple_of_3 O
  | SSS_multiple n (H : multiple_of_3 n) : multiple_of_3 (S (S (S n))).

Inductive multiple_of_3' : nat -> Prop :=
  | thirty_multiple : multiple_of_3' 30
  | twenty_one_multiple : multiple_of_3' 21
  | sum_multiple n m (H : multiple_of_3' n) (H' : multiple_of_3' m) : multiple_of_3' (n + m)
  | difference_multiple l n m (H : multiple_of_3' n) (H' : multiple_of_3' m) (H'' : l + n = m) : multiple_of_3' l.
```

### Prerequisites

A good command of a range of basic tactics and proof techniques in Coq.  Make sure you can complete most of the exercises in [Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html) up to and including "Inductively Defined Propositions" before attempting this Kata.

### General Guidelines

If in doubt, consult the [Coq standard library](https://coq.inria.fr/library/) for key definitions and useful lemmas.

### Too difficult?

You may want to try your hand at [A random fact about filtering](https://www.codewars.com/kata/5cb9dc6f98b230001cbe2cea) instead which only requires knowledge up to and including "More Basic Tactics" in Logical Foundations.

### Too easy?

Errr ... I'll try authoring more challenging Coq Kata in the near future ;)
~~~
~~~if:agda
### Preloaded.agda

```agda
{-# OPTIONS --without-K --safe #-}
module Preloaded where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

data Mult3 : ℕ → Set where
  0-mult : Mult3 0
  SSS-mult : ∀ n → Mult3 n → Mult3 (suc (suc (suc n)))

data Mult3' : ℕ → Set where
  30-mult : Mult3' 30
  21-mult : Mult3' 21
  sum-mult : ∀ n m → Mult3' n → Mult3' m → Mult3' (n + m)
  diff-mult : ∀ l n m → Mult3' n → Mult3' m → l + n ≡ m → Mult3' l
```
~~~
~~~if:idris
### Preloaded.idr

```idris
module Preloaded

%access public export
%default total

data Mult3 : Nat -> Type where
  Mult_0 : Mult3 0
  Mult_SSS : (n : Nat) -> Mult3 n -> Mult3 (S (S (S n)))
  
data Mult3' : Nat -> Type where
  Mult_30 : Mult3' 30
  Mult_21 : Mult3' 21
  Mult_sum : (n : Nat) -> (m : Nat) -> Mult3' n -> Mult3' m -> Mult3' (n + m)
  Mult_diff : (l : Nat) -> (n : Nat) -> (m : Nat) -> Mult3' n -> Mult3' m -> l + n = m -> Mult3' l
```
~~~
~~~if:lean
## Preloaded

The full source code for `Preloaded.lean` is displayed below for your reference:

```lean
inductive mult_3 : set ℕ
| mult_3_O :
    mult_3 0
| mult_3_SSS : ∀ n,
    mult_3 n →
    mult_3 (n + 3)

inductive mult_3' : set ℕ
| mult_3'_30 :
    mult_3' 30
| mult_3'_21 :
    mult_3' 21
| mult_3'_sum : ∀ n m,
    mult_3' n →
    mult_3' m →
    mult_3' (n + m)
| mult_3'_difference : ∀ l n m,
    mult_3' n →
    mult_3' m →
    l + n = m →
    mult_3' l

def SUBMISSION := mult_3 = mult_3'
notation `SUBMISSION` := SUBMISSION
```
~~~