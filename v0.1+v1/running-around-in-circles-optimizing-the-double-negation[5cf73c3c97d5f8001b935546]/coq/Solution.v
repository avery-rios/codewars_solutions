Require Import Preloaded.

Lemma optimize_notnot_neg : forall b st,
    beval st (optimize_notnot_b (~ b)) = negb (beval st (optimize_notnot_b b)).
Proof.
  intros b st. induction b; try reflexivity.
  - simpl in *. rewrite IHb. rewrite Bool.negb_involutive. reflexivity.
Qed.

Theorem optimize_notnot_b_sound : forall b st,
  beval st (optimize_notnot_b b) = beval st b.
Proof.
  intros b st. induction b; try reflexivity.
  - rewrite optimize_notnot_neg. simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
