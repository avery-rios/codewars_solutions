An interesting feature of Coq is that you can use the rewriting system on *your own data type* and *your own binary relation*. This is called [Generalized Rewriting](https://coq.inria.fr/distrib/current/refman/addendum/generalized-rewriting.html).

Using the feature, build a rewriting system in simple modular equivalence relation on `nat`.

The "simple" modular equivalence is defined as follows in Preloaded:

```coq
Inductive mod_equiv : nat -> nat -> nat -> Prop :=
  | mod_intro_same : forall m n, mod_equiv m n n
  | mod_intro_plus_l : forall m n1 n2, mod_equiv m n1 n2 -> mod_equiv m (m + n1) n2
  | mod_intro_plus_r : forall m n1 n2, mod_equiv m n1 n2 -> mod_equiv m n1 (m + n2).

(* Analogous to the mathematical notation `x == y (mod z)` *)
Notation "x == y %% z" := (mod_equiv z x y) (at level 70).

Notation "'x==x'" := mod_intro_same.
Notation "'m+x==y'" := mod_intro_plus_l.
Notation "'x==m+y'" := mod_intro_plus_r.
```

The following operations should be supported:

* Reflexivity
* Symmetry
* Transitivity
* Rewriting under `+` (plus) and `*` (mult).