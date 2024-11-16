Require Import Preloaded.

Module Introduction.

  (* Infinite sequence of ones. (not tested) *)
  CoFixpoint ones : stream nat := 1 :: ones.
  
  (* Infinite sequence of given value. *)
  CoFixpoint repeat {A : Set} (a : A) : stream A := a :: repeat a.
  
  (* Elements at even and odd indexes, respectively. *)
  CoFixpoint even {A : Set} (x : stream A) : stream A :=
    match x with
    | cons h (cons _ t) => cons h (even t)
    end.
  Definition odd {A : Set} (x : stream A) : stream A :=
    match x with
    | cons _ t => even t
    end.
  
  (* A stream equals its head plus its tail. (not tested) *)
  Lemma stream_unfold : forall {A : Set} (a : stream A), a = head a :: tail a.
  Proof. intros A a. destruct a. reflexivity. Qed.

End Introduction.

Module Bisimulation.
  
  Export Introduction.
  
  (* Bisimulation is reflexive. *)
  Theorem bisim_refl : forall {A : Set} (a : stream A), a == a.
  Proof.
    cofix CIH. intros A a. constructor.
    - reflexivity.
    - apply CIH.
  Qed.
  
  (* Odd is tail of Even. *)
  (* Hint: Do you really need cofix? It may depend on your own definition of odd and even. *)
  Theorem odd_even : forall {A : Set} (a : stream A), odd a == even (tail a).
  Proof.
    intros A a. destruct a. simpl. apply bisim_refl.
  Qed.
  
End Bisimulation.

Module Merge.

  Export Bisimulation.
  
  (* Interleave two streams, starting with the left one. *)
  CoFixpoint merge {A : Set} (x y : stream A) : stream A :=
    match x,y with
    | cons hx tx, cons hy ty => cons hx (cons hy (merge tx ty))
    end.
  
  (* Main task: Merge even and odd, and get the original. *)
  Theorem moe : forall {A : Set} (a : stream A), merge (even a) (odd a) == a.
  Proof.
    intros A. cofix CIH. intros a.
    destruct a as [a0 [a1 [a2 t]]]. simpl.
    constructor.
    - simpl. reflexivity.
    - simpl. constructor.
      + simpl. reflexivity.
      + simpl. apply CIH.
  Qed.

End Merge.
