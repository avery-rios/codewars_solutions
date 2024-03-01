Require Import Preloaded.
Require Import Arith Setoid Relation_Definitions Lia.

Theorem mod_eq_refl : forall m, reflexive nat (mod_equiv m).
Proof.
  intros m n. apply mod_intro_same.
Qed.

Theorem mod_eq_sym : forall m, symmetric nat (mod_equiv m).
Proof.
  intros m n1 n2 H. induction H.
  - apply mod_intro_same.
  - apply mod_intro_plus_r. assumption.
  - apply mod_intro_plus_l. assumption.
Qed.

Lemma mod_eq_inv : forall m n1 n2, mod_equiv m (m + n1) n2 -> mod_equiv m n1 n2.
Proof.
  intros m n1 n2 H. remember (m + n1) as nl. generalize dependent n1.
  induction H.
  - intros n1 Hn1. rewrite Hn1. apply mod_intro_plus_r. apply mod_intro_same.
  - intros nl Hnl. assert (n1 = nl) by lia. rewrite <- H0. assumption.
  - intros nl Hnl. apply mod_intro_plus_r. apply IHmod_equiv. assumption.
Qed.

Theorem mod_eq_trans : forall m, transitive nat (mod_equiv m).
Proof.
  intros m n1 n2 n3 H1 H2. induction H1.
  - assumption.
  - apply mod_intro_plus_l. apply IHmod_equiv. apply H2.
  - apply IHmod_equiv. apply mod_eq_inv. apply H2.
Qed.

Add Parametric Relation (m : nat) : nat (mod_equiv m)
  reflexivity proved by (mod_eq_refl m)
  symmetry proved by (mod_eq_sym m)
  transitivity proved by (mod_eq_trans m)
  as eq_mod_trans.

Add Parametric Morphism (m : nat) : Nat.add
  with signature (mod_equiv m) ==> (mod_equiv m) ==> (mod_equiv m)
  as mod_eq_plus.
Proof.
  intros x1 y1 H x2 y2 H2. induction H.
  - induction H2.
    + apply mod_intro_same.
    + replace (n + (m + n1)) with (m + (n + n1)); [| lia].
      apply mod_intro_plus_l. assumption.
    + replace (n + (m + n2)) with (m + (n + n2)); [| lia].
      apply mod_intro_plus_r. assumption.
  - rewrite <- Nat.add_assoc. apply mod_intro_plus_l.
    apply IHmod_equiv. apply H2.
  - rewrite <- Nat.add_assoc. apply mod_intro_plus_r.
    apply IHmod_equiv. apply H2.
Qed.

Lemma mod_eq_mul_m : forall m n, mod_equiv m (m * n) 0.
Proof.
  intros m n. rewrite Nat.mul_comm.
  induction n; simpl.
  - apply mod_intro_same.
  - apply mod_intro_plus_l. apply IHn.
Qed.

Add Parametric Morphism (m : nat) : Nat.mul
  with signature (mod_equiv m) ==> (mod_equiv m) ==> (mod_equiv m)
  as mod_eq_mul.
Proof.
  intros x1 y1 H x2 y2 H2. induction H.
  - induction n; simpl.
    + apply mod_intro_same.
    + apply mod_eq_plus; assumption.
  - rewrite Nat.mul_add_distr_r. rewrite <- (Nat.add_0_l (n2 * y2)).
    apply mod_eq_plus.
    + apply mod_eq_mul_m.
    + apply IHmod_equiv. apply H2.
  - rewrite Nat.mul_add_distr_r. rewrite <- (Nat.add_0_l (n1 * x2)).
    apply mod_eq_plus.
    + apply mod_eq_sym. apply mod_eq_mul_m.
    + apply IHmod_equiv. apply H2.
Qed.

(* Define anything you need in order to pass the tests! *)