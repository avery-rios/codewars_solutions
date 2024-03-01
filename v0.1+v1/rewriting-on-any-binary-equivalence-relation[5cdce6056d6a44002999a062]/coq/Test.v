Require Import Preloaded.
From Coq Require Import Setoid.
Require Solution.

Theorem refl_test : forall m n : nat, n == n %% m.
Proof. reflexivity. Qed.
Print Assumptions refl_test.

Theorem sym_trans_test : forall m n p q : nat, n == p %% m -> p == q %% m -> q == n %% m.
Proof. intros m n p q Hnp Hpq. symmetry. transitivity p; assumption. Qed.
Print Assumptions sym_trans_test.

Theorem rewrite_test : forall m n p q : nat, p == q %% m -> n == p + q %% m ->
  (n + (p + q)) * (n + (q + p)) == (q + p + n) * (p + q + n) %% m.
Proof. intros m n p q Hpq Hnpq. rewrite Hpq in Hnpq |- *. rewrite Hnpq. reflexivity. Qed.
Print Assumptions rewrite_test.