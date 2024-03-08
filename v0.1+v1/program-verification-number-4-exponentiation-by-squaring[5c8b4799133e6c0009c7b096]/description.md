~~~if:lean
Lean has the following implementation of the exponentiation function:

```lean
protected def pow (b : ℕ) : ℕ → ℕ
| 0        := 1
| (succ n) := pow n * b
```
~~~
~~~if:agda
Agda has the following implementation of the exponentiation function:

```agda
_^_ : ℕ → ℕ → ℕ
x ^ zero  = 1
x ^ suc n = x * x ^ n
```
~~~
~~~if:idris
Idris has the following implementation of the exponentiation function:

```idris
total power : Nat -> Nat -> Nat
power base Z       = S Z
power base (S exp) = mult base $ power base exp
```
~~~
~~~if:coq
Coq has the following definition of the exponentiation function:

```coq
Fixpoint pow n m :=
  match m with
    | 0 => 1
    | S m => n * (n^m)
  end

where "n ^ m" := (pow n m) : nat_scope.
```
~~~

The preloaded code contains the following definitions:

```lean
import data.nat.basic

open nat

-- The first argument (gas) helps Lean prove that
-- the function terminates
def pow_sqr_aux (gas : ℕ) : ℕ → ℕ → ℕ := nat.rec_on gas
  (λ _ _, 1)
  (λ gas' pow_sqr_aux_gas' b e, prod.cases_on
    (bodd_div2 e)
    (λ r e', bool.cases_on r
      (pow_sqr_aux_gas' (b * b) e')
      (b * pow_sqr_aux_gas' (b * b) e')))

def pow_sqr (b e : ℕ) : ℕ := pow_sqr_aux e b e

def SUBMISSION := ∀ b e : ℕ, pow_sqr b e = b ^ e
notation `SUBMISSION` := SUBMISSION
```
```agda
{-# OPTIONS --safe #-}
module Preloaded where

open import Data.Nat
open import Data.Product
open import Data.Bool

div-mod2 : ℕ → ℕ × Bool
div-mod2 0 = 0 , false
div-mod2 (suc 0) = 0 , true
div-mod2 (suc (suc n)) = let q , r = div-mod2 n in suc q , r

-- The first argument (k) helps Agda to prove
-- that the function terminates
pow-sqr-aux : ℕ → ℕ → ℕ → ℕ
pow-sqr-aux 0 _ _ = 1
pow-sqr-aux _ _ 0 = 1
pow-sqr-aux (suc k) b e with div-mod2 e
... | e' , false = pow-sqr-aux k (b * b) e'
... | e' , true = b * pow-sqr-aux k (b * b) e'

pow-sqr : ℕ → ℕ → ℕ
pow-sqr b e = pow-sqr-aux e b e
```
```idris
module Preloaded

%access public export
%default total

||| Divides a natural number by 2 and returns
||| the quotient and the remainder as a boolean value:
||| True = remainder is 1, False = remainder is 0.
divMod2 : Nat -> (Nat, Bool)
divMod2 Z = (Z, False)
divMod2 (S Z) = (Z, True)
divMod2 (S (S n)) = case divMod2 n of (q, r) => (S q, r)

-- The first argument (k) helps Idris to prove
-- that the function terminates.
powSqrAux : Nat -> Nat -> Nat -> Nat
powSqrAux Z _ _ = 1
powSqrAux _ _ Z = 1
powSqrAux (S k) b e =
    case divMod2 e of
        (e', False) => powSqrAux k (b * b) e'
        (e', True) => b * powSqrAux k (b * b) e'

powSqr : Nat -> Nat -> Nat
powSqr b e = powSqrAux e b e
```
```coq
Fixpoint div_mod2 (n : nat) : (nat * bool) :=
  match n with
  | 0 => (0, false)
  | 1 => (0, true)
  | S (S n) => let (a, b) := div_mod2 n in (S a, b)
  end.

(* The first argument (k) helps Coq to prove
   that the function terminates. *)
Fixpoint pow_sqr_aux (k b e : nat) : nat :=
  match k, e with
  | 0, _ => 1
  | _, 0 => 1
  | S k, _ => match div_mod2 e with
              | (e', false) => pow_sqr_aux k (b * b) e'
              | (e', true) => b * pow_sqr_aux k (b * b) e'
              end
  end.
  
Definition pow_sqr (b e : nat) : nat := pow_sqr_aux e b e.
```

~~~if:lean
Prove that

```lean
∀ b e : ℕ, pow_sqr b e = b ^ e
```
~~~
~~~if:agda
Prove that
```agda
pow-eq : ∀ b e → pow-sqr b e ≡ b ^ e
```
~~~
~~~if:idris
Prove that `powSqr b e = power b e` by implementing the following function:

```idris
powEq : (b, e : Nat) -> powSqr b e = power b e
powEq b e = ?write_a_proof
```

(Idris has several useful lemmas about `power`, see [Prelude.Nat.html](https://www.idris-lang.org/docs/current/prelude_doc/docs/Prelude.Nat.html) and [Nat.idr](https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Prelude/Nat.idr).)
~~~
~~~if:coq
Prove that
```coq
forall (b e : nat), pow_sqr b e = b ^ e.
```
~~~

## Similar Problems

Please check out the following collections for similar problems:

* [Program Verification](https://www.codewars.com/collections/program-verification-1)
* [Verified Sorting Algorithms](https://www.codewars.com/collections/verified-sorting-algorithms) by [@donaldsebleung](https://www.codewars.com/users/donaldsebleung)  
* [Verified Algorithms](https://www.codewars.com/collections/5d0e575208985f000f6e5671) by [@dramforever](https://www.codewars.com/users/dramforever)