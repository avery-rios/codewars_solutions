Require Solution.
Require Import Preloaded.

Ltac test_begin x := idtac ""; idtac "<DESCRIBE::> Testing" x; idtac "".
Ltac test_end := idtac ""; idtac "<COMPLETEDIN::>"; idtac "".

Theorem EM_impl_LPO_test : EM -> LPO.
Proof.
  test_begin EM_impl_LPO. Print Assumptions Solution.EM_impl_LPO. test_end.
  exact Solution.EM_impl_LPO.
Qed.

Theorem LPO_impl_LLPO_test : LPO -> LLPO.
Proof.
  test_begin LPO_impl_LLPO. Print Assumptions Solution.LPO_impl_LLPO. test_end.
  exact Solution.LPO_impl_LLPO.
Qed.