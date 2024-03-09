Require Solution.
Require Import Preloaded.
From CW Require Import Loader.

Definition cmax_exists := exists cmax, forall c, capprox c cmax.

CWGroup "Solution.cmax_exists_dec".
  CWTest "should have the correct type".
    CWAssert Solution.cmax_exists_dec : (cmax_exists \/ ~ cmax_exists).
  CWTest "should be closed under the global context".
    CWAssert Solution.cmax_exists_dec Assumes.
CWEndGroup.