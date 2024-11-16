Require Import Preloaded.
Open Scope conat_scope.
Require Solution.

Theorem plus_comm_test : forall n m, n + m == m + n.
Proof. exact Solution.plus_comm. Qed.
Print Assumptions plus_comm_test.

Theorem plus_assoc_test : forall n m p, (n + m) + p == n + (m + p).
Proof. exact Solution.plus_assoc. Qed.
Print Assumptions plus_assoc_test.