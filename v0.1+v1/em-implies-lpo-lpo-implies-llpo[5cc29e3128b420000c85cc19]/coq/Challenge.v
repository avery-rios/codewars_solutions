Require Import Arith.
Require Import Preloaded.
Import Nat.

Theorem EM_impl_LPO : EM -> LPO.
Proof. 
  intros EM f. destruct (EM (exists n, f n = true)).
  - right. apply H.
  - left. intros n. destruct (f n) eqn:Ef.
    + exfalso. apply H. exists n. apply Ef.
    + reflexivity.
Qed.

Theorem LPO_impl_LLPO : LPO -> LLPO.
Proof. 
  intros LPO f Huniq. destruct (LPO f) as [H | [n Ef]].
  - left. intros n _. apply H.
  - assert (Hneq : forall m, even m = negb (even n) -> f m = false).
      { intros m Hnp. destruct (Huniq n m).
        - intros E. apply (Bool.no_fixpoint_negb (even n)). congruence.
        - congruence.
        - apply H. }
    destruct (even n) eqn:Ee.
    + right. simpl in Hneq. apply Hneq.
    + left. simpl in Hneq. apply Hneq.
Qed.
      