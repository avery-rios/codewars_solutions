## Prerequisites

* Recommended
  * [Yet another introduction to bisimulation, Chicken's style](https://www.codewars.com/kata/5cbd5a3d9f1a4e0018503301)
* Optional
  * [Nat in the mirror (Idris)](https://www.codewars.com/kata/5c84a95c71c5210f2930c481)
  * [Nat in the mirror: "Not finite" implies "Infinite"](https://www.codewars.com/kata/5cc15c2628b42000147b6ed8)
  * [Rewriting on any binary equivalence relation](https://www.codewars.com/kata/5cdce6056d6a44002999a062)

## Task

Given the definition of co-inductive natural number `conat`, bisimulation `bisim` and addition `plus`:

```coq
CoInductive conat : Set :=
  | O : conat
  | S : conat -> conat.

CoInductive bisim : conat -> conat -> Prop :=
  | OO : bisim O O
  | SS : forall n m, bisim n m -> bisim (S n) (S m).

Notation "x == y" := (bisim x y) (at level 80) : conat_scope.

CoFixpoint plus (n m : conat) : conat := match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) : conat_scope.
```

Prove that `plus` is both commutative and associative.

```coq
Open Scope conat_scope.
Theorem plus_comm : forall n m, n + m == m + n.
Theorem plus_assoc : forall n m p, (n + m) + p == n + (m + p).
```

## But isn't it impossible?

At some point in the proof of `plus_comm`, it is necessary to apply transitivity with `plus_n_Sm`:

```coq
Theorem bisim_trans : forall n m p, n == m -> m == p -> n == p.
Theorem plus_n_Sm : forall n m, n + S m == S (n + m).
```

However, putting the cofix call under `bisim_trans` makes the proof unguarded, so Coq rejects it. Then how should we complete the proof?

## It *is* possible.

We can generalize the theorem so that the arguments to `bisim_trans` go under the cofix call:

```coq
(* instead of this goal *)
s == t
(* use this goal *)
forall s' t', s'== s -> t == t' -> s' == t'
```

This technique is called Coinduction Loading, and exactly how and why it works in Coq is described in Chapter 3 of [this paper](https://people.irisa.fr/Martin.Bodin/paperoj/itp13.pdf). You don't need to fully understand its theory to the end.

Once you understand what's going on in this paper, having a rewriting system on `bisim` might help.