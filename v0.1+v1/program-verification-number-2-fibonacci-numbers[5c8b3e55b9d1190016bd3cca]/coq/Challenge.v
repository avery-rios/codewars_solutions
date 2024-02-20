From Coq Require Import Arith.
Require Import Preloaded.

(* Preloaded:

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n as n') => fib n' + fib n
  end.

Fixpoint fib_aux (a b n : nat) : nat :=
  match n with
  | 0 => a
  | S n => fib_aux b (a + b) n
  end.
  
Definition fib2 (n : nat) : nat := fib_aux 0 1 n.

*)

Lemma fib_aux_next : forall n k, fib_aux (fib k) (fib (S k)) n = fib (k + n).
Proof.
  induction n; intros k.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn delta [fib_aux] fix. cbn iota.
    replace (fib k + fib (S k)) with (fib (S (S k))).
    + rewrite IHn. f_equal. simpl. rewrite <- plus_n_Sm. reflexivity.
    + rewrite Nat.add_comm. reflexivity.
Qed.

Theorem fib_eq (n : nat) : fib2 n = fib n.
Proof.
  replace (fib n) with (fib (0 + n)).
  - rewrite <- fib_aux_next. unfold fib2. f_equal.
  - reflexivity.
Qed.
  