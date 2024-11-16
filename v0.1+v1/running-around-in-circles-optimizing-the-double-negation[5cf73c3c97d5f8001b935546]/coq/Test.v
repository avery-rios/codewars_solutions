Require Import Preloaded.
Require Solution.

Theorem optimize_notnot_b_sound_test : forall b st, beval st (optimize_notnot_b b) = beval st b.
Proof.
  exact Solution.optimize_notnot_b_sound.
Qed.
Print Assumptions Solution.optimize_notnot_b_sound.