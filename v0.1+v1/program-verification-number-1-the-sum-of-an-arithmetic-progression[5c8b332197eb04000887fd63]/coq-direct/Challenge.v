From Coq Require Import Arith.
Require Import Preloaded.

(* Preloaded:
Require Import Arith.

Fixpoint arith_sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => n + arith_sum m
  end.

Definition arith_formula (n : nat) : nat := Nat.div2 (n * (n + 1)).
*)

Require Import Lia.

Import Nat.

Theorem arith_eq (n : nat) : arith_formula n = arith_sum n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. unfold arith_formula.
    replace (S (n + div2 (n * (n + 1)))) with (div2 (2 + 2 * n + n * (n + 1))).
    + f_equal. lia.
    + rewrite div2_div. rewrite div2_div. 
      rewrite <- div_add_l; [| discriminate]. rewrite <- (add_1_l (_ / 2)).
      rewrite <- div_add_l; [| discriminate]. f_equal. lia.
Qed.