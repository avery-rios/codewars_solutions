Require Import Preloaded.

From Coq Require Import List Ascii.
Import ListNotations.
Import PeanoNat.Nat.

Local Open Scope char_scope.

Require Import Lia.

Theorem leftpad_length : forall c n s,
  length (leftpad c n s) = max n (length s).
Proof. 
  intros c n s. unfold leftpad. rewrite app_length. rewrite repeat_length.
  lia.
Qed.

Theorem leftpad_prefix : forall c n s,
  Forall (fun p => p = c) (firstn (n - length s) (leftpad c n s)).
Proof. 
  intros c n s. unfold leftpad. rewrite firstn_app.
  rewrite repeat_length. rewrite sub_diag. simpl. rewrite app_nil_r.
  rewrite firstn_all2.
  - rewrite Forall_forall. apply repeat_spec.
  - rewrite repeat_length. apply le_refl.
Qed.

Theorem leftpad_suffix: forall c n s,
  skipn (n - length s) (leftpad c n s) = s.
Proof.
  intros c n s. unfold leftpad. rewrite skipn_app.
  rewrite skipn_all2.
  - simpl. rewrite repeat_length. rewrite sub_diag. reflexivity.
  - rewrite repeat_length. apply le_refl.
Qed.

