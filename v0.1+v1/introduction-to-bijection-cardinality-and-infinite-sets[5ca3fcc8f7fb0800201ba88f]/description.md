## Introduction

In elementary set theory, a [**bijection**](https://en.wikipedia.org/wiki/Bijection) between two sets `A` and `B` are defined as follows:

* A bijection is a function `f` from `A` to `B`
* ... which has a function `g` from `B` to `A`
* ... where `f` and `g` are inverse functions of each other:
  * For any element `a` of set `A`, `g (f a) == a`.
  * For any element `b` of set `B`, `f (g b) == b`.

~~~if:agda
The following shows one possible representation of a bijection in Agda:
~~~

~~~if:coq
The following shows one possible representation of a bijection in Coq:
~~~

~~~if:lean
The following shows one possible representation of a bijection in Lean:
~~~

```agda
-- Preloaded code
{-# OPTIONS --safe #-}
module Iso where

open import Relation.Binary.PropositionalEquality public
open import Data.Nat public

record _⇔_ (A B : Set) : Set where
  constructor Bijection
  field
    A→B : A → B
    B→A : B → A
    A→B→A : ∀ (a : A) → B→A (A→B a) ≡ a
    B→A→B : ∀ (b : B) → A→B (B→A b) ≡ b
```
```coq
Record iso (A B : Set) : Set :=
  bijection {
    A_to_B : A -> B;
    B_to_A : B -> A;
    A_B_A  : forall a : A, B_to_A (A_to_B a) = a;
    B_A_B  : forall b : B, A_to_B (B_to_A b) = b
  }.
```
```lean
structure iso (A : Type) (B : Type) :=
  (a_to_b : A → B)
  (b_to_a : B → A)
  (a_b_a : ∀ a, b_to_a (a_to_b a) = a)
  (b_a_b : ∀ b, a_to_b (b_to_a b) = b)
```

(NB: it is [the exact way Iso is defined in Idris](https://github.com/idris-lang/Idris-dev/blob/c4c03b6ef666273a3f36ddb0e6efe3e487726139/libs/base/Control/Isomorphism.idr).)

Two sets `A` and `B` are defined to have the same size, or **cardinality**, when there exists a bijection between `A` and `B`. Note that it is sufficient to provide *any* bijection to prove this property.

## Task

~~~if:agda
Prove some various properties of `_⇔_` in general, then prove that `ℕ` has the same cardinality as some supersets of itself. Note that `ℕ×ℕ` is not covered here because it's much harder to prove than the other statements.

Infinite sets, the most basic one being `ℕ`, have such weird properties. You can read about [Hilbert's Hotel paradox](https://en.wikipedia.org/wiki/Hilbert%27s_paradox_of_the_Grand_Hotel) if you haven't heard of it already.

## Key bindings

```
Enter this | to enter this
--------------------------
\bN        | ℕ
\<=>       | ⇔
\all       | ∀
\r         | →
\Gl        | λ
\==        | ≡
```
~~~

~~~if:coq
Prove some various properties of `iso` in general, then prove that `nat` has the same cardinality as some supersets of itself. Note that `nat × nat` is not covered here because it's much harder to prove than the other statements.

Infinite sets, the most basic one being `nat`, have such weird properties. You can read about [Hilbert's Hotel paradox](https://en.wikipedia.org/wiki/Hilbert%27s_paradox_of_the_Grand_Hotel) if you haven't heard of it already.
~~~

~~~if:lean
Prove some various properties of `iso` in general, then prove that `nat` has the same cardinality as some supersets of itself. Note that `nat × nat` is not covered here because it's much harder to prove than the other statements.

Infinite sets, the most basic one being `nat`, have such weird properties. You can read about [Hilbert's Hotel paradox](https://en.wikipedia.org/wiki/Hilbert%27s_paradox_of_the_Grand_Hotel) if you haven't heard of it already.
~~~