From Coq Require Import ZArith.

Require Import Lia.

Open Scope Z.

Theorem int_induction : forall (P : Z -> Prop) (m : Z),
  (forall n, n <= m -> P n) ->
  (forall n, m <= n -> P n -> P (Z.succ n)) ->
  forall n, P n.
Proof. 
  intros P m Hl Hi n.
  assert (Hm : P m). { apply Hl. apply Z.le_refl. }
  assert (Hp : forall k, P (Zpos k + m)).
    { induction k using Pos.peano_ind.
      - rewrite Z.add_1_l. apply Hi.
        + apply Z.le_refl.
        + apply Hm.
      - rewrite Pos2Z.inj_succ. rewrite Z.add_succ_l. apply Hi.
        + lia.
        + apply IHk.
    }
  replace (n) with ((n - m) + m); [ | lia].
  destruct (n - m).
  - simpl. apply Hm.
  - apply Hp.
  - apply Hl. lia.
Qed.

Close Scope Z.
