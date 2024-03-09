Require Import Preloaded.

Definition cmax_exists := exists cmax, forall c, capprox c cmax.

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

Theorem cmax_exists_dec : cmax_exists \/ ~ cmax_exists.
Proof.
  right. intros [cmx H].
  assert (Hc1: empty_st =[ X ::= 1 ]=> (X !-> 1)).
    { apply E_Ass. reflexivity. }
  assert (Hc2: empty_st =[ X ::= 2 ]=> (X !-> 2)).
    { apply E_Ass. reflexivity. }
  
  apply H in Hc1. apply H in Hc2. clear H.
  specialize (ceval_deterministic _ _ _ _ Hc1 Hc2) as Hm.
  assert (contra: 1 = 2).
    { replace 2 with ((X !-> 2) X).
      - rewrite <- Hm. reflexivity.
      - reflexivity. }
  discriminate contra.
Qed.
