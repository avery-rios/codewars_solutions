CoInductive stream (A : Set) : Set :=
  | cons : A -> stream A -> stream A.
Arguments cons {_} hd tl.

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Definition head {A} (x : stream A) := match x with
  hd :: _ => hd end.
Definition tail {A} (x : stream A) := match x with
  _ :: tl => tl end.

CoInductive bisim {A : Set} (x y : stream A) : Set :=
  | bisim_eq : head x = head y -> bisim (tail x) (tail y) -> bisim x y.
Notation "x == y" := (bisim x y) (at level 70).

