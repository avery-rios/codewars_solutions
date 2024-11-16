Require Import Preloaded.
Require Solution.
From Coq Require List.
From Coq Require String.

CoFixpoint ones := 1 :: ones.
Definition repeat {A} := @Solution.Introduction.repeat A.
Definition even {A} := @Solution.Introduction.even A.
Definition odd {A} := @Solution.Introduction.odd A.

Definition bisim_refl {A} := @Solution.Bisimulation.bisim_refl A.
Definition odd_even {A} := @Solution.Bisimulation.odd_even A.

Definition merge {A} := @Solution.Merge.merge A.
Definition moe {A} := @Solution.Merge.moe A.

Fixpoint take {A : Set} (n : nat) (x : stream A) : list A := match n with
  | O => nil
  | S n' => List.cons (head x) (take n' (tail x)) end.
  
Goal True. idtac "<DESCRIBE::> Testing repeat". idtac "". Abort.
Example repeat_test1 : List.repeat 1 10 = take 10 (repeat 1).
Proof. reflexivity. Qed.
Example repeat_test2 : List.repeat 2 20 = take 20 (repeat 2).
Proof. reflexivity. Qed.
Print Assumptions repeat.
Goal True. idtac "<COMPLETEDIN::>". idtac "". Abort.

Goal True. idtac "<DESCRIBE::> Testing even". idtac "". Abort.
CoFixpoint onetwo : stream nat := 1 :: 2 :: onetwo.
CoFixpoint onetwothree : stream nat := 1 :: 2 :: 3 :: onetwothree.
CoFixpoint onethreetwo : stream nat := 1 :: 3 :: 2 :: onethreetwo.
Example even_test1 : take 10 (even onetwo) = take 10 ones.
Proof. reflexivity. Qed.
Example even_test2 : take 20 (even onetwothree) = take 20 onethreetwo.
Proof. reflexivity. Qed.
Print Assumptions even.
Goal True. idtac "<COMPLETEDIN::>". idtac "". Abort.

Goal True. idtac "<DESCRIBE::> Testing odd". idtac "". Abort.
Example odd_test1 : take 10 (odd onetwo) = List.repeat 2 10.
Proof. reflexivity. Qed.
Example odd_test2 : take 20 (odd onetwothree) = take 20 (2 :: onethreetwo).
Proof. reflexivity. Qed.
Print Assumptions odd.
Goal True. idtac "<COMPLETEDIN::>". idtac "". Abort.

Goal True. idtac "<DESCRIBE::> Testing bisim_refl". idtac "". Abort.
Theorem bisim_refl_test : forall {A : Set} (a : stream A), a == a.
Proof. exact @bisim_refl. Qed.
Print Assumptions bisim_refl_test.

Goal True. idtac "<DESCRIBE::> Testing odd_even". idtac "". Abort.
Theorem odd_even_test : forall {A : Set} (a : stream A), odd a == even (tail a).
Proof. exact @odd_even. Qed.
Print Assumptions odd_even_test.
Goal True. idtac "<COMPLETEDIN::>". idtac "". Abort.

Goal True. idtac "<DESCRIBE::> Testing merge". idtac "". Abort.
Example merge_test1 : take 20 (merge (repeat 1) (repeat 2)) = take 20 onetwo.
Proof. reflexivity. Qed.
Example merge_test2 : take 20 (merge onetwothree (3 :: onetwothree)) = take 20 onethreetwo.
Proof. reflexivity. Qed.
Print Assumptions merge.
Goal True. idtac "<COMPLETEDIN::>". idtac "". Abort.

Goal True. idtac "<DESCRIBE::> Testing moe". idtac "". Abort.
Theorem moe_test : forall {A : Set} (a : stream A), merge (even a) (odd a) == a.
Proof. exact @moe. Qed.
Print Assumptions moe_test.
Goal True. idtac "<COMPLETEDIN::>". idtac "". Abort.