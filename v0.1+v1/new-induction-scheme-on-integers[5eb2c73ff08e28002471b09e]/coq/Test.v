Require Solution.
From Coq Require Import ZArith.
From CW Require Import Loader.

Open Scope Z.

CWGroup "Solution.int_induction".
  CWTest "should have the correct type".
    CWAssert Solution.int_induction : (forall (P : Z -> Prop) (m : Z),
      (forall n, n <= m -> P n) ->
      (forall n, m <= n -> P n -> P (Z.succ n)) ->
      forall n, P n).
  CWTest "should be closed under the global context".
    CWAssert Solution.int_induction Assumes.
CWEndGroup.

Close Scope Z.