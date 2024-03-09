Require Solution.
Require Import Preloaded.
From CW Require Import Loader.

Definition seq_if_dist_l := forall b c1 c2 c3, cequiv
  (TEST b THEN c1 ;; c2 ELSE c1 ;; c3 FI)
  (c1 ;; TEST b THEN c2 ELSE c3 FI).

CWGroup "Solution.seq_if_dist_l_dec".
  CWTest "should have the correct type".
    CWAssert Solution.seq_if_dist_l_dec : (seq_if_dist_l \/ ~ seq_if_dist_l).
  CWTest "should be closed under the global context".
    CWAssert Solution.seq_if_dist_l_dec Assumes.
CWEndGroup.