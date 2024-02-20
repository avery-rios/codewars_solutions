## Introduction

The [Law of Excluded Middle](https://en.wikipedia.org/wiki/Law_of_excluded_middle) (EM) is a famous classical axiom that cannot be proven inside intuitionistic logic.

~~~if:coq
EM states that, for any given statement, it holds or its negation holds. In Coq:

```coq
Definition EM := forall A : Prop, A \/ ~ A.
```
~~~
~~~if:agda
EM states that, for any given statement, it holds or its negation holds. In Agda:

```agda
EM = (A : Set) → A ⊎ ¬ A
```
~~~

There are also [Limited Principle of Omniscience](https://en.wikipedia.org/wiki/Limited_principle_of_omniscience) (LPO) and its lesser version (LLPO). These statements are also nonconstructive, but weaker than EM.

LPO states that, for any boolean sequence `a_0, a_1, ...`, either of the following holds:

* every `a_i` is false, or
* there exists a `k` such that `a_k` is true.

~~~if:coq
If we interpret the sequence as a function from `nat` to `bool`, the equivalent Coq type is:

```coq
Definition LPO := forall (f : nat -> bool),
  (forall n : nat, f n = false) \/ (exists n : nat, f n = true).
```
~~~
~~~if:agda
If we interpret the sequence as a function from `nat` to `bool`, the equivalent Agda type is:

```agda
LPO = (f : ℕ → Bool) → (∀ n → f n ≡ false) ⊎ (∃ λ n → f n ≡ true)
```
~~~

LLPO states that, for any boolean sequence `a_0, a_1, ...` such that at most one `a_i` is true, either of the following holds:

* every element at the even index is false, or
* every element at the odd index is false.

~~~if:coq
In Coq:

```coq
Definition LLPO := forall (f : nat -> bool),
  (forall n m : nat, n <> m -> f n = false \/ f m = false) ->
    (forall n : nat, even n = true  -> f n = false) \/
    (forall n : nat, even n = false -> f n = false).
```
~~~
~~~if:agda
In Agda:

```coq
LLPO = (f : ℕ → Bool) → (∀ n m → n ≢ m → f n ≡ false ⊎ f m ≡ false) →
  (∀ n → even n ≡ true → f n ≡ false) ⊎ (∀ n → even n ≡ false → f n ≡ false)

```
~~~

## Task

Prove that EM implies LPO, and LPO implies LLPO.

Note that, for both statements, the converse is not provable.