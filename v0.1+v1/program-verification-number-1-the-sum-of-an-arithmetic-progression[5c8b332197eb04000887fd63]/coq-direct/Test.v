Require Import Preloaded.
Require Solution.
From CW Require Import Loader.

CWGroup "arith_eq".
  CWTest "arith_eq type".
    CWAssert Solution.arith_eq : 
      (forall (n : nat), arith_formula n = arith_sum n).
        
  CWTest "arith_eq assumptions".
    CWAssert Solution.arith_eq Assumes.
CWEndGroup.