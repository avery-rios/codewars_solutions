From Coq Require Import List Ascii.
Import ListNotations.

Require Import Preloaded.
Require Solution.
From CW Require Import Loader.

CWTest "Test leftpad_length".
  CWAssert Solution.leftpad_length :
    (forall c n s, length (leftpad c n s) = max n (length s)).
  CWAssert Solution.leftpad_length Assumes.
CWEndTest.

CWTest "Test leftpad_prefix".
  CWAssert Solution.leftpad_prefix :
    (forall c n s, Forall (fun p => p = c) (firstn (n - length s) (leftpad c n s))).
  CWAssert Solution.leftpad_prefix Assumes.
CWEndTest.

CWTest "Test leftpad_suffix".
  CWAssert Solution.leftpad_suffix :
    (forall c n s, skipn (n - length s) (leftpad c n s) = s).
  CWAssert Solution.leftpad_suffix Assumes.
CWEndTest.
