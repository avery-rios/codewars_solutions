From Coq Require Import List Ascii.
Import ListNotations.

Definition leftpad (c : ascii) (n : nat) (s : list ascii) :=
  repeat c (n - length s) ++ s.

