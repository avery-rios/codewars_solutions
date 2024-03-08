Require Preloaded.
Require Solution.
From CW Require Import Loader.

CWGroup "pow_eq".
  CWTest "pow_eq type".
    CWAssert Solution.pow_eq : 
      (forall (b e : nat), 
        Preloaded.pow_sqr b e = Nat.pow b e).
        
  CWTest "pow_eq assumptions".
    CWAssert Solution.pow_eq Assumes.
CWEndGroup.