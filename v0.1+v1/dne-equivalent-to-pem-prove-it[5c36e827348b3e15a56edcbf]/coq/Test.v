Require Solution.

Definition axiom_pem := forall (P : Prop), P \/ ~P.

Definition axiom_dne := forall (P : Prop), ~ ~P -> P.

Example from_test : axiom_dne -> axiom_pem.
Proof. exact Solution.from. Qed.

Print Assumptions from_test.

Example to_test : axiom_pem -> axiom_dne.
Proof. exact Solution.to. Qed.

Print Assumptions to_test.