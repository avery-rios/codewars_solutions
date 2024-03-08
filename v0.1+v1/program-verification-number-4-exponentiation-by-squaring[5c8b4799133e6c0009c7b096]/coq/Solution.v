From Coq Require Import Arith Div2.
Require Import Lia.
Require Import Preloaded.

Definition ind2 P (P0 : P 0) (P1 : P 1) (Pk : forall k, P k -> P (S (S k))) :
  forall n, P n :=
  let fix f n :=
    match n with
    | 0 => P0
    | 1 => P1
    | S (S k) => Pk k (f k)
    end
  in f.

Lemma div2_inv : forall n n1 b,
  div_mod2 n = (n1, b) -> 
  (if b then 1 else 0) + n1 + n1 = n.
Proof.
  induction n using ind2; intros n1 b Ed.
  - injection Ed as En1 Eb. subst. reflexivity.
  - injection Ed as Eb1 Eb. subst. reflexivity.
  - simpl in Ed. destruct (div_mod2 n). injection Ed as En1 Eb. subst.
    rewrite <- (IHn n0 b); [| reflexivity]. lia.
Qed.

Lemma pow_eq_k : forall k b e, e <= k -> pow_sqr_aux k b e = b ^ e.
Proof.
  induction k; intros b e Hl.
  - inversion Hl. reflexivity.
  - simpl. destruct e. { reflexivity. }
    destruct (div_mod2 (S e)) as [e1 ls] eqn:Ee1. apply div2_inv in Ee1.
    rewrite IHk.
    + simpl. rewrite <- Nat.pow_2_r. rewrite <- Nat.pow_mul_r.
      simpl. rewrite Nat.add_0_r.
      destruct ls; simpl in *.
      * injection Ee1 as Ee. rewrite Ee. reflexivity.
      * rewrite Ee1. reflexivity.
    + lia.
Qed.

Theorem pow_eq (b e : nat) : pow_sqr b e = b ^ e.
Proof. apply pow_eq_k. auto. Qed.