Require Import Preloaded.

Definition seq_if_dist_r := forall b c1 c2 c3, cequiv
  (TEST b THEN c1 ;; c3 ELSE c2 ;; c3 FI)
  (TEST b THEN c1 ELSE c2 FI ;; c3).

Theorem seq_if_dist_r_dec :
  seq_if_dist_r \/ ~ seq_if_dist_r.
Proof.
  left. intros b c1 c2 c3 st st'.
  split; intros H.
  - inversion H; inversion H6; subst; clear H H6.
    + eapply E_Seq.
        { apply E_IfTrue; [assumption |]. apply H9. }
        { assumption. }
    + eapply E_Seq.
        { apply E_IfFalse; [assumption |]. apply H9. }
        { assumption. }
  - inversion H; inversion H2; subst; clear H H2.
    + apply E_IfTrue; [assumption |]. eapply E_Seq; eauto.
    + apply E_IfFalse; [assumption |]. eapply E_Seq; eauto.
Qed.
