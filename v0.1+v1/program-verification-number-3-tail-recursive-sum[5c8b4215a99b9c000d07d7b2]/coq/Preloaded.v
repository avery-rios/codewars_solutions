Fixpoint sum_simple (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S m => f n + sum_simple f m
  end.

Fixpoint sum_aux (a : nat) (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0 + a
  | S m => sum_aux (f n + a) f m
  end.

Definition sum_tail := sum_aux 0.

