Require Import Preloaded.


Lemma nvalue_nf : forall v t, nvalue v -> ~ (v --> t).
Proof.
  intros v t Hv H. induction H; try inversion Hv.
  - apply IHstep. inversion Hv. auto.
Qed.

Lemma lvalue_nf : forall v t, lvalue v -> ~ (v --> t).
Proof.
  intros v t Hv H. induction H; try solve [inversion Hv].
  - apply IHstep. inversion Hv; auto.
  - inversion Hv; subst. apply (nvalue_nf t1 t1'); assumption.
Qed.

Theorem step_deterministic : deterministic step.
Proof.
  intros x y1 y2 Hy1. generalize dependent y2.
  induction Hy1; intros y2 Hy2; inversion Hy2; subst;
      try reflexivity;
      match goal with
      | Hv: nvalue ?v, Ht: ?v --> ?t |- _ =>
          exfalso; apply (nvalue_nf v t); auto
      | Ht: zro --> ?t |- _ =>
          exfalso; apply (nvalue_nf zro t nv_zro Ht)
      | Hv: nvalue ?v, Ht: scc ?v --> ?t |- _ =>
          exfalso; exact (nvalue_nf (scc v) t (nv_scc _ Hv) Ht)
      | Ht: nul --> ?t |- _ =>
          inversion Ht
      | Hvh: nvalue ?h, Hvt: lvalue ?t, Ht: cns ?h ?t --> ?t1 |- _ =>
          exfalso; refine (lvalue_nf (cns h t) t1 _ Ht);
            constructor; auto
      | _ => repeat f_equal; auto
      end.
Qed.

Lemma nat_canonical : forall v, |- v \in Nat -> value v -> nvalue v.
Proof.
  intros v Ht Hv. destruct Hv.
  - assumption.
  - destruct H.
    + inversion Ht.
    + inversion Ht.
Qed.

Lemma idx_nul_typed : |- idx zro nul \in Nat.
Proof.
  apply T_Idx.
  - apply T_Zro.
  - apply T_Nul.
Qed.

Lemma idx_nul_not_value : ~ value (idx zro nul).
Proof.
  intros Hv. destruct Hv as [Hv | Hv]; inversion Hv.
Qed.

Lemma idx_nul_stuck : forall t, ~ (idx zro nul --> t).
Proof.
  intros t Hst. inversion Hst; subst.
  - inversion H3.
  - inversion H2.
Qed.

Theorem progress_dec : progress \/ ~ progress.
Proof.
  right. intros H.
  specialize (H _ _ idx_nul_typed). destruct H as [Hv | [t' Hst]].
  - exact (idx_nul_not_value Hv).
  - exact (idx_nul_stuck _ Hst).
Qed.

Lemma nvalue_Nat : forall v, nvalue v -> |- v \in Nat.
Proof.
  intros v Hv. induction Hv.
  - apply T_Zro.
  - apply T_Scc. apply IHHv.
Qed.

Lemma lvalue_List : forall v, lvalue v -> |- v \in List.
Proof.
  intros v Hv. induction Hv.
  - apply T_Nul.
  - apply T_Cns.
    + apply nvalue_Nat. apply H.
    + exact IHHv.
Qed.

Theorem preservation_dec : preservation \/ ~ preservation.
Proof.
  left. intros t t' T Ht. generalize dependent t'.
  induction Ht; intros t' Hst; inversion Hst; subst;
    try solve [constructor; auto].
  - apply nvalue_Nat. assumption.
  - apply T_Scc. apply T_Pls.
    + apply nvalue_Nat. assumption.
    + apply nvalue_Nat. assumption.
  - apply T_Scc. apply T_Len. apply lvalue_List. assumption.
  - apply nvalue_Nat. assumption.
  - apply T_Idx.
    + apply nvalue_Nat. assumption.
    + apply lvalue_List. assumption.
  - apply T_Cns.
    + apply nvalue_Nat. assumption.
    + apply T_Nul.
Qed.

Corollary soundness_dec : soundness \/ ~ soundness.
Proof.
  right. intros H.
  specialize (H _ _ _ idx_nul_typed (multi_refl _ _)).
  apply H. split.
  - intros Hn. destruct Hn as [t' Hst].
    exact (idx_nul_stuck _ Hst).
  - exact idx_nul_not_value.
Qed.

