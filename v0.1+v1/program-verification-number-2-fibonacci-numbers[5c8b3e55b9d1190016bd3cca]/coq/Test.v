Require Preloaded.
Require Solution.
From CW Require Import Loader.

CWGroup "fib_eq".
  CWTest "fib_eq type".
    CWAssert Solution.fib_eq : 
      (forall (n : nat), Preloaded.fib2 n = Preloaded.fib n).
        
  CWTest "fib_eq assumptions".
    CWAssert Solution.fib_eq Assumes.
CWEndGroup.