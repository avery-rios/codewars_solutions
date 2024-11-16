Require Solution.
Require Import Preloaded.
From CW Require Import Loader.

CWGroup "Properties of our toy language".
  CWTest "Determinism of step".
    CWAssert Solution.step_deterministic : (deterministic step).
    CWAssert Solution.step_deterministic Assumes.
  CWTest "The progress property for our type system".
    CWAssert Solution.progress_dec : (progress \/ ~ progress).
    CWAssert Solution.progress_dec Assumes.
  CWTest "The preservation property for our type system".
    CWAssert Solution.preservation_dec : (preservation \/ ~ preservation).
    CWAssert Solution.preservation_dec Assumes.
  CWTest "Type soundnesss of our type system".
    CWAssert Solution.soundness_dec : (soundness \/ ~ soundness).
    CWAssert Solution.soundness_dec Assumes.
CWEndGroup.