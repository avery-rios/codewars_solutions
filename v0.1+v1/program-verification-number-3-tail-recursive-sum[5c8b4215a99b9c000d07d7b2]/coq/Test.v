Require Preloaded.
Require Solution.
From CW Require Import Loader.

CWGroup "sum_eq".
  CWTest "sum_eq type".
    CWAssert Solution.sum_eq : 
      (forall (f : nat -> nat) (n : nat),
        Preloaded.sum_tail f n = Preloaded.sum_simple f n).
        
  CWTest "sum_eq assumptions".
    CWAssert Solution.sum_eq Assumes.
CWEndGroup.