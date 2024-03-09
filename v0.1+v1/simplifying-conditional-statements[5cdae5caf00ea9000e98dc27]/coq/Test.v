Require Solution.
Require Import Preloaded.
From CW Require Import Loader.

Definition seq_if_dist_r := forall b c1 c2 c3, cequiv
  (TEST b THEN c1 ;; c3 ELSE c2 ;; c3 FI)
  (TEST b THEN c1 ELSE c2 FI ;; c3).

CWGroup "Solution.seq_if_dist_r_dec".
  CWTest "should have the correct type".
    CWAssert Solution.seq_if_dist_r_dec : (seq_if_dist_r \/ ~ seq_if_dist_r).
  CWTest "should be closed under the global context".
    CWAssert Solution.seq_if_dist_r_dec Assumes.
CWEndGroup.