Require Import Preloaded.

Definition seq_if_dist_l := forall b c1 c2 c3, cequiv
  (TEST b THEN c1 ;; c2 ELSE c1 ;; c3 FI)
  (c1 ;; TEST b THEN c2 ELSE c3 FI).

Theorem seq_if_dist_l_dec :
  seq_if_dist_l \/ ~ seq_if_dist_l.
Proof.
  right. intros H.
  remember (BEq X 0) as b.
  remember (CAss X 1) as c1.
  remember (CAss Y 1) as c2. remember (CAss Y 2) as c3.
  assert (Hc1 : empty_st =[ TEST b THEN c1 ;; c2 ELSE c1 ;; c3 FI]=>
    (Y !-> 1; X !-> 1)).
    { subst. apply E_IfTrue; [reflexivity|]. eapply E_Seq.
      - apply E_Ass. reflexivity.
      - apply E_Ass. reflexivity. }
  assert (Hc2 : empty_st =[ c1 ;; TEST b THEN c2 ELSE c3 FI ]=>
    (Y !-> 2; X !-> 1)).
    { subst. eapply E_Seq.
      - apply E_Ass. reflexivity.
      - apply E_IfFalse; [reflexivity |]. apply E_Ass. reflexivity. }

  apply H in Hc1. subst.
  inversion Hc1. inversion H2. subst. clear Hc1 H2.
  inversion H5; subst; clear H5.
  - discriminate H6.
  - inversion H7. subst. simpl in H4.
    assert (contra: 2 = 1).
      { replace 2 with ((Y !-> 2; X !-> 1) Y).
        + rewrite H4. reflexivity.
        + reflexivity. }
    discriminate contra.
Qed.
