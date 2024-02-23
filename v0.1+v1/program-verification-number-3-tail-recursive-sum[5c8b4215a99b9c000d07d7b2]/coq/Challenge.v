From Coq Require Import Arith.
Require Import Preloaded.

Import Nat.
Require Import Lia.

Lemma sum_aux_eq (f : nat -> nat): forall n a,
  sum_aux a f n = a + sum_simple f n.
Proof.
  induction n; intros a.
  - simpl. apply add_comm.
  - simpl. rewrite IHn. lia.
Qed.

Theorem sum_eq (f : nat -> nat) (n : nat) : sum_tail f n = sum_simple f n.
Proof. 
  unfold sum_tail. rewrite sum_aux_eq. reflexivity.
Qed.