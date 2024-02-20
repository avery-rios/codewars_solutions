Require Import Arith.

Fixpoint arith_sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => n + arith_sum m
  end.

Definition arith_formula (n : nat) : nat := Nat.div2 (n * (n + 1)).

