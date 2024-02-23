~~~if:idris
We can compute the sum `f(1) + ... + f(n)` in the following way:
~~~
~~~if:agda,coq,lean
We can compute the sum `f(0) + f(1) + ... + f(n)` in the following way:
~~~

```idris
sumSimple : (Nat -> Nat) -> Nat -> Nat
sumSimple _ Z = Z
sumSimple f (S n) = f (S n) + sumSimple f n
```
```agda
sumSimple : (ℕ → ℕ) → ℕ → ℕ
sumSimple f zero = f zero
sumSimple f (suc n) = f (suc n) + sumSimple f n
```
```coq
Fixpoint sum_simple (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S m => f n + sum_simple f m
  end.
```
```lean
def sum_simple (f : ℕ → ℕ) : ℕ → ℕ
| 0       := f 0
| n@(m+1) := f n + sum_simple m
```

We can also implement a tail-recursive version of this function:

```idris
sumAux : Nat -> (Nat -> Nat) -> Nat -> Nat
sumAux acc _ Z = acc
sumAux acc f (S n) = sumAux (f (S n) + acc) f n

sumTail : (Nat -> Nat) -> Nat -> Nat
sumTail = sumAux 0
```
```agda
sumAux : ℕ → (ℕ → ℕ) → ℕ → ℕ
sumAux acc f zero = f zero + acc
sumAux acc f (suc n) = sumAux (f (suc n) + acc) f n

sumTail : (ℕ → ℕ) → ℕ → ℕ
sumTail = sumAux zero
```
```coq
Fixpoint sum_aux (a : nat) (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0 + a
  | S m => sum_aux (f n + a) f m
  end.

Definition sum_tail := sum_aux 0.
```
```lean
def sum_aux : ℕ → (ℕ → ℕ) → ℕ → ℕ
| a f 0       := f 0 + a
| a f n@(m+1) := sum_aux (f n + a) f m

def sum_tail := sum_aux 0
```

~~~if:idris
Your task is to prove that `sumTail f n = sumSimple f n` by implementing the following function:

```idris
sumEq : (f : Nat -> Nat) -> (n : Nat) -> sumTail f n = sumSimple f n
sumEq f n = ?write_a_proof
```
~~~
~~~if:agda
Your task is to prove that `sumTail f n ≡ sumSimple f n` by implementing the following function:

```agda
sumEq : (f : ℕ → ℕ) → (n : ℕ) → sumTail f n ≡ sumSimple f n
sumEq = ?
```
~~~
~~~if:coq
Your task is to prove that 
```coq
forall f n, sum_tail f n = sum_simple f n
```
~~~
~~~if:lean
Your task is to prove the following result
```lean
theorem sum_eq (f n) : sum_tail f n = sum_simple f n := ...
```
~~~

## Similar Problems

Please check out the following collections for similar problems:

* [Program Verification](https://www.codewars.com/collections/program-verification-1)
* [Verified Sorting Algorithms](https://www.codewars.com/collections/verified-sorting-algorithms) by [@donaldsebleung](https://www.codewars.com/users/donaldsebleung)  
* [Verified Algorithms](https://www.codewars.com/collections/5d0e575208985f000f6e5671) by [@dramforever](https://www.codewars.com/users/dramforever)