Require Import Nat.

Definition EM := forall A : Prop, A \/ ~ A.

Definition LPO := forall (f : nat -> bool),
  (forall n : nat, f n = false) \/ (exists n : nat, f n = true).

Definition LLPO := forall (f : nat -> bool),
  (forall n m : nat, n <> m -> f n = false \/ f m = false) ->
    (forall n : nat, even n = true  -> f n = false) \/
    (forall n : nat, even n = false -> f n = false).

