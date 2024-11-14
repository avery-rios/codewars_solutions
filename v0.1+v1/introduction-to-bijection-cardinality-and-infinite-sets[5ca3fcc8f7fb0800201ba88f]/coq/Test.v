Require Solution.
Require Import Preloaded.

Ltac test_begin x := idtac ""; idtac "<DESCRIBE::> Testing" x; idtac "".
Ltac test_end := idtac ""; idtac "<COMPLETEDIN::>"; idtac "".

Theorem iso_refl_test : forall A : Set, iso A A.
Proof.
  test_begin iso_refl. Print Assumptions Solution.iso_refl. test_end.
  exact Solution.iso_refl. Qed.

Theorem iso_sym_test : forall A B : Set, iso A B -> iso B A.
Proof.
  test_begin iso_sym. Print Assumptions Solution.iso_sym. test_end.
  exact Solution.iso_sym. Qed.

Theorem iso_trans_test : forall A B C : Set, iso A B -> iso B C -> iso A C.
Proof.
  test_begin iso_trans. Print Assumptions Solution.iso_trans. test_end.
  exact Solution.iso_trans. Qed.

Theorem bijection_alt_test : forall (A B : Set) (A2B : A -> B) (B2A : B -> A),
  (forall a, B2A (A2B a) = a) -> (forall b1 b2, B2A b1 = B2A b2 -> b1 = b2) -> iso A B.
Proof.
  test_begin bijection_alt. Print Assumptions Solution.bijection_alt. test_end.
  exact Solution.bijection_alt. Qed.

Theorem nat_iso_natp1_test : iso nat nat_plus_1.
Proof.
  test_begin nat_iso_natp1. Print Assumptions Solution.nat_iso_natp1. test_end.
  exact Solution.nat_iso_natp1. Qed.

Theorem nat_iso_natpnat_test : iso nat nat_plus_nat.
Proof.
  test_begin nat_iso_natpnat. Print Assumptions Solution.nat_iso_natpnat. test_end.
  exact Solution.nat_iso_natpnat. Qed.