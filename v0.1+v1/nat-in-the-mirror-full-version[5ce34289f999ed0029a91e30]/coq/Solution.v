Require Import Preloaded.
Open Scope conat_scope.

Lemma bisim_refl : forall n, n == n.
Proof.
  cofix CIH. intros n. destruct n.
  - apply OO.
  - apply SS. apply CIH.
Qed.

Lemma bisim_symm : forall n m, n == m -> m == n.
Proof.
  cofix CIH. intros n m H. destruct H.
  - apply OO.
  - apply SS. apply CIH. apply H.
Qed.

Lemma bisim_trans : forall n m p, n == m -> m == p -> n == p.
Proof.
  cofix CIH. intros n. destruct n.
  - intros m p Hm Hp. inversion Hm. subst. inversion Hp. subst.
    apply OO.
  - intros m p Hm Hp. inversion Hm. subst. inversion Hp. subst.
    apply SS. eapply CIH; eassumption.
Qed.

Definition eval (n : conat) :=
  match n with
  | O => O
  | S n => S n
  end.

Lemma eval_eq : forall n, n = eval n.
Proof.
  intros n. destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Lemma add_0_r : forall n, n == n + O.
Proof.
  cofix CIH. intros n. destruct n.
  - rewrite (eval_eq (O+O)). simpl. apply OO.
  - rewrite (eval_eq (plus _ _)). simpl.
    apply SS. apply CIH.
Qed.

Lemma add_n_Sm : forall n m, n + S m == S (n + m).
Proof.
  cofix CIH. intros n m. destruct n.
  - rewrite (eval_eq (O + S m)). simpl. rewrite (eval_eq (O + m)). simpl.
    destruct m; apply bisim_refl.
  - rewrite (eval_eq (S n + S m)). rewrite (eval_eq (S n + m)). simpl.
    apply SS. apply CIH.
Qed.

Lemma plus_comm' : forall n l m r, n + m == l -> r == m + n -> l == r.
Proof.
  cofix CIH. intros n l m r Hnt Hmt. destruct n.
  - apply (bisim_trans _ m).
    + apply (bisim_trans _ (O+m)).
      * apply bisim_symm. exact Hnt.
      * rewrite (eval_eq (O+m)). simpl. destruct m; apply bisim_refl.
    + apply (bisim_trans _ (m+O)).
      * apply add_0_r.
      * apply bisim_symm. assumption.
  - rewrite (eval_eq (S n + m)) in Hnt. simpl in Hnt. inversion Hnt. subst.
    assert (Hr : r == S (m + n)).
      { apply (bisim_trans _ (m + S n)).
        - assumption.
        - apply add_n_Sm. }
    inversion Hr. subst.
    apply SS. apply (CIH n _ m).
    + assumption.
    + apply (bisim_trans _ _ (S (m + n))) in Hmt; [| apply add_n_Sm].
      inversion Hmt. subst. assumption.
Qed.

Theorem plus_comm : forall n m, n + m == m + n.
Proof.
  intros n m. apply (plus_comm' n _ m _); apply bisim_refl.
Qed.

Lemma plus_assoc' : forall n m p l r,
  (n + m) + p == l ->
  r == n + (m + p) ->
  l == r.
Proof.
  cofix CIH. intros n m p l r Hl Hr.
  destruct n.
  - rewrite (eval_eq (O + m + p)) in Hl. simpl in Hl.
    rewrite (eval_eq (O + (m + p))) in Hr. simpl in Hr.
    apply bisim_symm. eapply bisim_trans.
    + exact Hr.
    + exact Hl.
  - rewrite (eval_eq (S n + m + p)) in Hl. simpl in Hl.
    rewrite (eval_eq (S n + (m + p))) in Hr. simpl in Hr.
    inversion Hl. subst. inversion Hr. subst.
    apply SS. apply (CIH n m p); assumption.
Qed.

Theorem plus_assoc : forall n m p, (n + m) + p == n + (m + p).
Proof.
  intros. apply (plus_assoc' n m p); apply bisim_refl.
Qed.
