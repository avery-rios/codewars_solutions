Require Import Preloaded.
Require Import Arith.

Theorem multiple_of_3_iff_multiple_of_3' :
  forall n, multiple_of_3 n <-> multiple_of_3' n.
Proof.
  split.
  - assert (Hm3 : multiple_of_3' 3).
    { assert (Hm9 : multiple_of_3' 9).
        { apply (difference_multiple 9 21 30).
          - constructor.
          - constructor.
          - reflexivity. }
      apply (difference_multiple 3 18 21).
      - exact (sum_multiple 9 9 Hm9 Hm9).
      - constructor.
      - reflexivity. }
    intros H. induction H.
    + apply (difference_multiple 0 3 3); auto.
    + apply (sum_multiple 3 n); assumption.
  - intros H. induction H.
    + repeat apply SSS_multiple. apply O_multiple.
    + repeat apply SSS_multiple. apply O_multiple.
    + assert (Hm_add : multiple_of_3 n -> multiple_of_3 m -> multiple_of_3 (n + m)).
      { clear. intros Hn. induction Hn.
        - trivial.
        - intros Hm. simpl. apply SSS_multiple.
          exact (IHHn Hm). }
      apply Hm_add; assumption.
    + assert (Hm_sub : n + l = m -> multiple_of_3 n -> multiple_of_3 m -> multiple_of_3 l).
        { clear. intros E Hn. generalize dependent m.
          induction Hn.
          - simpl. intros m E Hm. rewrite E. exact Hm.
          - simpl. intros m E Hm. subst m. inversion Hm; subst.
            apply (IHHn (n + l)); auto. }
      rewrite Nat.add_comm in H''.
      apply Hm_sub; assumption.
Qed.
