Inductive multiple_of_3 : nat -> Prop :=
  | O_multiple : multiple_of_3 O
  | SSS_multiple n (H : multiple_of_3 n) : multiple_of_3 (S (S (S n))).

Inductive multiple_of_3' : nat -> Prop :=
  | thirty_multiple : multiple_of_3' 30
  | twenty_one_multiple : multiple_of_3' 21
  | sum_multiple n m (H : multiple_of_3' n) (H' : multiple_of_3' m) : multiple_of_3' (n + m)
  | difference_multiple l n m (H : multiple_of_3' n) (H' : multiple_of_3' m) (H'' : l + n = m) : multiple_of_3' l.

