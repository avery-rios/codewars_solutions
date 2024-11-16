Require Solution.
Require Import Preloaded.
From CW Require Import Loader.

CWGroup "Solution.multiple_of_3_iff_multiple_of_3'".
  CWTest "should have the correct type".
    CWAssert Solution.multiple_of_3_iff_multiple_of_3' :
      (forall n, multiple_of_3 n <-> multiple_of_3' n).
  CWTest "should be closed under the global context".
    CWAssert Solution.multiple_of_3_iff_multiple_of_3' Assumes.
CWEndGroup.