Inductive mod_equiv : nat -> nat -> nat -> Prop :=
  | mod_intro_same : forall m n, mod_equiv m n n
  | mod_intro_plus_l : forall m n1 n2, mod_equiv m n1 n2 -> mod_equiv m (m + n1) n2
  | mod_intro_plus_r : forall m n1 n2, mod_equiv m n1 n2 -> mod_equiv m n1 (m + n2).

(* Analogous to the mathematical notation `x == y (mod z)` *)
Notation "x == y %% z" := (mod_equiv z x y) (at level 70).

Notation "'x==x'" := mod_intro_same.
Notation "'m+x==y'" := mod_intro_plus_l.
Notation "'x==m+y'" := mod_intro_plus_r.
