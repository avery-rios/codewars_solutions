(This is part of a series of 'Verified' kata, where a classical algorithm problem is posed, the specification is formalized, the algorithm is implemented, and you're asked to prove the algorithm's correctness. Check out [the collection of all 'Verified' kata](https://www.codewars.com/collections/5d0e575208985f000f6e5671))

## Background

Some time ago there was ['The great theorem prover showdown' by Hillel Wayne][showdown]. The goal was to challenge the notion that purely functional code is easier to reason than imperative code. The challenge was to write formally verified purely functional algorithms and compare them to the formally verified imperative Dafny code provided. Although the author of this kata does not necessarily agree with all points in the blog post, the challenges are well selected and are good exercises in formal proving/verification no matter imperative or functional. We're doing one today.

[showdown]: https://www.hillelwayne.com/post/theorem-prover-showdown/

(You can check out all Theorem prover showdown kata as a [collection][showdown-collection]).

[showdown-collection]: https://www.codewars.com/collections/5ef384425e64a1002ee4a9d0

(I have asked and obtained permission to turn the challenges into Codewars kata.)

## The problem

It's a common text formatting task to pad a string to a certain length. We're specifically interested in a 'leftpad'.

Given a padding character `c` and a target length `n`, to leftpad a string `s`, we add `c` on the left of of `s` until it is at least `n` long and return the result. Specifically if the length of `s` is already `n` or more, we return `s` unmodified.

We'd like to verify the following three properties regarding `c`, `n`, `s` and the padded string `s'`:

- `len(s') = max{n, len(s)}`
- The first `max{0, n - len(s)}` characters of `s`  are all `c`.
- The rest of `s'` is the same as `s`.

## The formalization

~~~if:coq
We are going to use `list ascii` for strings. `ascii` prints like `"x"` in `char_scope` for eye candy. Otherwise, the details are of no use in this kata; it really could have been any other type or even polymorphic.
~~~
~~~if:lean
We are going to use `list char` for strings. The `char` type represents an unicode scalar value. Otherwise, the details are of no use in this kata; it really could have been any other type or even polymorphic.
~~~

The algorithm is implemented functionally in a pretty elegant way:

```coq
Definition leftpad (c : ascii) (n : nat) (s : list ascii) :=
  repeat c (n - length s) ++ s.
```
```lean
def leftpad (c : char) (n : ℕ) (s : list char) :=
  list.repeat c (n - s.length) ++ s
```

~~~if:coq,lean
Note: `nat` is automatically capped at zero for subtraction, so `n - length s` really means `max (n - length s) 0`. It's a happy coincidence that we can use this fact here.
~~~

And the theorems you need to prove are:

```coq
Theorem leftpad_length : forall c n s,
  length (leftpad c n s) = max n (length s).
Proof. (* FILL IN HERE *) Admitted.

Theorem leftpad_prefix : forall c n s,
  Forall (fun p => p = c) (firstn (n - length s) (leftpad c n s)).
Proof. (* FILL IN HERE *) Admitted.

Theorem leftpad_suffix: forall c n s,
  skipn (n - length s) (leftpad c n s) = s.
Proof. (* FILL IN HERE *) Admitted.
```
```lean
variables (c : char) (n : ℕ) (s : list char)

theorem leftpad_length :
  (leftpad c n s).length = max n s.length :=
sorry

theorem leftpad_prefix :
  ∀ p ∈ list.take (n - s.length) (leftpad c n s), p = c :=
sorry

theorem leftpad_suffix :
  list.drop (n - s.length) (leftpad c n s) = s :=
sorry
```

## Hints

~~~if:coq
- The [documentation of `Lists`][doc-lists] contains the definition of `firstn`, `Forall`, etc. and many useful results about list operations.

[doc-lists]: https://coq.inria.fr/library/Coq.Lists.List.html
~~~
~~~if:lean
- The [basic properties of `lists`][mathlib] contain many useful results about list operations.

[mathlib]: https://leanprover-community.github.io/mathlib_docs/data/list/basic.html
~~~

## Preloaded code

```coq
From Coq Require Import List Ascii.
Import ListNotations.

Definition leftpad (c : ascii) (n : nat) (s : list ascii) :=
  repeat c (n - length s) ++ s.
```
```lean
def leftpad (c : char) (n : ℕ) (s : list char) :=
  list.repeat c (n - s.length) ++ s
```
