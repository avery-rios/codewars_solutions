Require Import Preloaded.
Require Import Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

(* Task 0 : Example of iso in finite sets *)
(* Find a bijection between bool and bit. (provided for you as an example) *)
Inductive bit : Set := b0 | b1.

Definition bool2bit (b : bool) : bit :=
  match b with true => b1 | false => b0
  end.

Definition bit2bool (b : bit) : bool :=
  match b with b1 => true | b0 => false
  end.

Definition bool_iso_bit : iso bool bit.
Proof. apply (bijection _ _ bool2bit bit2bool); intros []; auto. Qed.

(******************************************)
(* Task 1 : General properties of iso *)
(* Task 1-1. Prove that any set has the same cardinality as itself. *)
Theorem iso_refl : forall A : Set, iso A A.
Proof.
  intros A.
  refine (bijection A A (fun a => a) (fun a => a) _ _); reflexivity.
Qed.

(* Task 1-2. Prove that iso is symmetric. *)
Theorem iso_sym : forall A B : Set, iso A B -> iso B A.
Proof.
  exact (fun A B i => 
    bijection B A
      (B_to_A _ _ i)
      (A_to_B _ _ i)
      (B_A_B _ _ i)
      (A_B_A _ _ i)).
Qed.

(* Task 1-3. Prove that iso is transitive. *)
Theorem iso_trans : forall A B C : Set, iso A B -> iso B C -> iso A C.
Proof.
  intros A B C ab bc.
  refine (bijection A C
    (fun a => A_to_B _ _ bc (A_to_B _ _ ab a))
    (fun c => B_to_A _ _ ab (B_to_A _ _ bc c))
    _
    _).
  - intros a. rewrite (A_B_A _ _ bc). apply (A_B_A _ _ ab).
  - intros c. rewrite (B_A_B _ _ ab). apply (B_A_B _ _ bc).
Qed.

(* Task 1-4. Prove the following statement:
  Given two functions A->B and B->A, if A->B->A is satisfied and B->A is injective, A <=> B. *)
Theorem bijection_alt : forall (A B : Set) (A2B : A -> B) (B2A : B -> A),
  (forall a, B2A (A2B a) = a) -> (forall b1 b2, B2A b1 = B2A b2 -> b1 = b2) -> iso A B.
Proof.
  intros A B A2B B2A Hr Hi.
  refine (bijection A B A2B B2A Hr _).
  intros b. apply Hi.
  rewrite Hr. reflexivity.
Qed.

(******************************************)
(* Task 2 : iso relations between nat and various supersets of nat *)

(* nat_plus_1 : a set having one more element than nat. (provided in preloaded) *)

(* Task 2-1. Prove that nat has the same cardinality as nat_plus_1. *)
Theorem nat_iso_natp1 : iso nat nat_plus_1.
Proof.
  refine (bijection _ _
    (fun n => match n with
              | O => null
              | S n' => is_nat n'
              end)
    (fun n1 => match n1 with
               | null => O
               | is_nat n' => S n'
               end)
    _ _).
  - intros a. destruct a; reflexivity.
  - intros b. destruct b; reflexivity.
Qed.

(* nat_plus_nat : a set having size(nat) more elements than nat. (provided in preloaded) *)

Fixpoint nat_to_nat_plus_nat (n : nat) :=
  match n with
  | O => left O
  | S n' =>
      match nat_to_nat_plus_nat n' with
      | left l => right l
      | right r => left (S r)
      end
  end.

(* Task 2-2. Prove that nat has the same cardinality as nat_plus_nat. *)
Theorem nat_iso_natpnat : iso nat nat_plus_nat.
Proof.
  refine (bijection _ _
    nat_to_nat_plus_nat
    (fun l =>
      match l with
      | left n => 2 * n
      | right n => S (2 * n)
      end)
    _ _).
  - induction a.
    + reflexivity.
    + simpl. destruct (nat_to_nat_plus_nat a); lia.
  - intros [|].
    + induction n.
      * reflexivity.
      * simpl in *. rewrite Nat.add_succ_r. simpl.
        rewrite IHn. reflexivity.
    + induction n.
      * reflexivity.
      * simpl in *. rewrite Nat.add_succ_r. simpl.
        rewrite IHn. reflexivity.
Qed.
