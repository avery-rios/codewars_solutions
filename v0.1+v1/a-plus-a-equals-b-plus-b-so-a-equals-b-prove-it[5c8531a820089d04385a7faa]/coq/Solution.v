Require Import Arith.

Theorem invert : forall a b : nat, a + a = b + b -> a = b.
Proof.
  induction a; intros b H.
  - simpl in H. destruct b.
    + reflexivity.
    + simpl in H. discriminate H.
  - simpl in H. destruct b. { discriminate H. }
    simpl in H. rewrite Nat.add_succ_r in H. rewrite Nat.add_succ_r in H.
    injection H as H. apply IHa in H.
    rewrite H. reflexivity.
Qed.
