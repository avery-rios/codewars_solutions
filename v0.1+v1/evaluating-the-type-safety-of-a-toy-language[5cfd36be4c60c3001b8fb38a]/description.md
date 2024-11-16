_This Kata is part of a collection of [supplementary exercises for Programming Language Foundations](https://www.codewars.com/collections/supplementary-exercises-for-programming-language-foundations)._

# Evaluating the type safety of a toy language

*The key definitions, concepts and notations presented in this Kata are inspired by the* [Software Foundations](https://softwarefoundations.cis.upenn.edu) *series, an excellent resource for learning Coq.*

## Prerequisites

Make sure you have read and understood the content presented in [Type Systems (Types)](https://softwarefoundations.cis.upenn.edu/plf-current/Types.html) of [Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/current/plf-current/index.html).

## Background

*NOTE: You do not need to copy the code examples presented in this Section into your IDE just yet - the full Preloaded source code will be repeated in a later section.*

Consider a toy language consisting of only numeric values and lists of numeric values (we won't consider polymorphism here) as well as some basic operations on them such as addition of natural numbers, length of a list, indexed access of elements in a list and constructing singleton lists from numbers:

```coq
Inductive tm : Type :=
  | zro : tm
  | scc : tm -> tm
  | pls : tm -> tm -> tm
  | nul : tm
  | cns : tm -> tm -> tm
  | len : tm -> tm
  | idx : tm -> tm -> tm
  | stn : tm -> tm.
```
```lean
inductive tm : Type
  | zro : tm
  | scc : tm -> tm
  | pls : tm -> tm -> tm
  | nul : tm
  | cns : tm -> tm -> tm
  | len : tm -> tm
  | idx : tm -> tm -> tm
  | stn : tm -> tm
open tm
```

A value is either a number or a list:

```coq
Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall v1, nvalue v1 -> nvalue (scc v1).

Inductive lvalue : tm -> Prop :=
  | lv_nul : lvalue nul
  | lv_cns : forall v1 v2,
      nvalue v1 -> lvalue v2 -> lvalue (cns v1 v2).

Definition value (t : tm) := nvalue t \/ lvalue t.
```
```lean
inductive nvalue : tm -> Prop
  | nv_zro : nvalue zro
  | nv_scc : Π v1, nvalue v1 -> nvalue (scc v1)
open nvalue

inductive lvalue : tm -> Prop
  | lv_nul : lvalue nul
  | lv_cns : Π v1 v2,
      nvalue v1 -> lvalue v2 -> lvalue (cns v1 v2)

def value (t : tm) := nvalue t ∨ lvalue t
```

We then define the small-step operational semantics for our toy language:

```coq
Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      scc t1 --> scc t1'
  | ST_PlsZro : forall v1,
      nvalue v1 ->
      pls zro v1 --> v1
  | ST_PlsScc : forall v1 v2,
      nvalue v1 ->
      nvalue v2 ->
      pls (scc v1) v2 --> scc (pls v1 v2)
  | ST_Pls2 : forall v1 t2 t2',
      nvalue v1 ->
      t2 --> t2' ->
      pls v1 t2 --> pls v1 t2'
  | ST_Pls1 : forall t1 t1' t2,
      t1 --> t1' ->
      pls t1 t2 --> pls t1' t2
  | ST_Cns2 : forall v1 t2 t2',
      nvalue v1 ->
      t2 --> t2' ->
      cns v1 t2 --> cns v1 t2'
  | ST_Cns1 : forall t1 t1' t2,
      t1 --> t1' ->
      cns t1 t2 --> cns t1' t2
  | ST_LenNul :
      len nul --> zro
  | ST_LenCns : forall v1 v2,
      nvalue v1 ->
      lvalue v2 ->
      len (cns v1 v2) --> scc (len v2)
  | ST_Len : forall t1 t1',
      t1 --> t1' ->
      len t1 --> len t1'
  | ST_IdxZro : forall v1 v2,
      nvalue v1 ->
      lvalue v2 ->
      idx zro (cns v1 v2) --> v1
  | ST_IdxScc : forall v1 v2 v3,
      nvalue v1 ->
      nvalue v2 ->
      lvalue v3 ->
      idx (scc v1) (cns v2 v3) --> idx v1 v3
  | ST_Idx2 : forall v1 t2 t2',
      nvalue v1 ->
      t2 --> t2' ->
      idx v1 t2 --> idx v1 t2'
  | ST_Idx1 : forall t1 t1' t2,
      t1 --> t1' ->
      idx t1 t2 --> idx t1' t2
  | ST_StnNval : forall v1,
      nvalue v1 ->
      stn v1 --> cns v1 nul
  | ST_Stn : forall t1 t1',
      t1 --> t1' ->
      stn t1 --> stn t1'

where "t1 '-->' t2" := (step t1 t2).
```
```lean
inductive step : tm -> tm -> Prop
notation x  ` ⟶ `:100 y := step x y
  | ST_Scc : ∀ t1 t1',
      (t1 ⟶ t1') →
      scc t1 ⟶ scc t1'
  | ST_PlsZro : ∀ v1,
      nvalue v1 →
      pls zro v1 ⟶ v1
  | ST_PlsScc : ∀ v1 v2,
      nvalue v1 →
      nvalue v2 →
      pls (scc v1) v2 ⟶ scc (pls v1 v2)
  | ST_Pls2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      pls v1 t2 ⟶ pls v1 t2'
  | ST_Pls1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      pls t1 t2 ⟶ pls t1' t2
  | ST_Cns2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      cns v1 t2 ⟶ cns v1 t2'
  | ST_Cns1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      cns t1 t2 ⟶ cns t1' t2
  | ST_LenNul :
      len nul ⟶ zro
  | ST_LenCns : ∀ v1 v2,
      nvalue v1 →
      lvalue v2 →
      len (cns v1 v2) ⟶ scc (len v2)
  | ST_Len : ∀ t1 t1',
      (t1 ⟶ t1') →
      len t1 ⟶ len t1'
  | ST_IdxZro : ∀ v1 v2,
      nvalue v1 →
      lvalue v2 →
      idx zro (cns v1 v2) ⟶ v1
  | ST_IdxScc : ∀ v1 v2 v3,
      nvalue v1 →
      nvalue v2 →
      lvalue v3 →
      idx (scc v1) (cns v2 v3) ⟶ idx v1 v3
  | ST_Idx2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      idx v1 t2 ⟶ idx v1 t2'
  | ST_Idx1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      idx t1 t2 ⟶ idx t1' t2
  | ST_StnNval : ∀ v1,
      nvalue v1 →
      stn v1 ⟶ cns v1 nul
  | ST_Stn : ∀ t1 t1',
      (t1 ⟶ t1') →
      stn t1 ⟶ stn t1'
open step

infix ` ⟶ `:100 := step
```

There are only two types of expressions in our toy language: `Nat` and `List`:

```coq
Inductive ty : Type :=
  | Nat : ty
  | List : ty.
```
```lean
inductive ty : Type
  | Nat : ty
  | List : ty
open ty
```

The typing relation for our language is as follows:

```coq
Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Zro :
      |- zro \in Nat
  | T_Scc : forall t1,
      |- t1 \in Nat ->
      |- scc t1 \in Nat
  | T_Pls : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in Nat ->
      |- pls t1 t2 \in Nat
  | T_Nul :
      |- nul \in List
  | T_Cns : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in List ->
      |- cns t1 t2 \in List
  | T_Len : forall t1,
      |- t1 \in List ->
      |- len t1 \in Nat
  | T_Idx : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in List ->
      |- idx t1 t2 \in Nat
  | T_Stn : forall t1,
      |- t1 \in Nat ->
      |- stn t1 \in List

where "'|-' t '\in' T" := (has_type t T).
```
```lean
inductive has_type : tm → ty → Prop
notation `⊢ `:79 t ` :∈ `:80 T := has_type t T
  | T_Zro :
      ⊢ zro :∈ Nat

  | T_Scc : ∀ t1,
      (⊢ t1 :∈ Nat) →
      ⊢ scc t1 :∈ Nat
  | T_Pls : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ Nat) →
      ⊢ pls t1 t2 :∈ Nat

  | T_Nul :
      ⊢ nul :∈ List
  | T_Cns : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ List) →
      ⊢ cns t1 t2 :∈ List

  | T_Len : ∀ t1,
      (⊢ t1 :∈ List) →
      (⊢ len t1 :∈ Nat)
  | T_Idx : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ List) →
      ⊢ idx t1 t2 :∈ Nat
  | T_Stn : ∀ t1,
      (⊢ t1 :∈ Nat) →
      ⊢ stn t1 :∈ List
open has_type

notation `⊢ `:19 t ` :∈ `:20 T := has_type t T
```

Make sure you understand the definitions presented above and what they mean before moving on to the main task.

## Task

First confirm that we haven't messed up our single-step relation by proving that it is deterministic. Then determine whether each of the following properties hold for our toy language:

- Progress
- Preservation

Hence, or otherwise, determine whether the type system for our toy language is sound.

## Gentle Reminder

Try to leverage automation where possible - otherwise, the proofs in this Kata can get *very* long ;-)

## Preloaded.v

The full source code of the Preloaded section is displayed below for your reference:

```coq
Inductive tm : Type :=
  | zro : tm
  | scc : tm -> tm
  | pls : tm -> tm -> tm
  | nul : tm
  | cns : tm -> tm -> tm
  | len : tm -> tm
  | idx : tm -> tm -> tm
  | stn : tm -> tm.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall v1, nvalue v1 -> nvalue (scc v1).

Inductive lvalue : tm -> Prop :=
  | lv_nul : lvalue nul
  | lv_cns : forall v1 v2,
      nvalue v1 -> lvalue v2 -> lvalue (cns v1 v2).

Definition value (t : tm) := nvalue t \/ lvalue t.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      scc t1 --> scc t1'
  | ST_PlsZro : forall v1,
      nvalue v1 ->
      pls zro v1 --> v1
  | ST_PlsScc : forall v1 v2,
      nvalue v1 ->
      nvalue v2 ->
      pls (scc v1) v2 --> scc (pls v1 v2)
  | ST_Pls2 : forall v1 t2 t2',
      nvalue v1 ->
      t2 --> t2' ->
      pls v1 t2 --> pls v1 t2'
  | ST_Pls1 : forall t1 t1' t2,
      t1 --> t1' ->
      pls t1 t2 --> pls t1' t2
  | ST_Cns2 : forall v1 t2 t2',
      nvalue v1 ->
      t2 --> t2' ->
      cns v1 t2 --> cns v1 t2'
  | ST_Cns1 : forall t1 t1' t2,
      t1 --> t1' ->
      cns t1 t2 --> cns t1' t2
  | ST_LenNul :
      len nul --> zro
  | ST_LenCns : forall v1 v2,
      nvalue v1 ->
      lvalue v2 ->
      len (cns v1 v2) --> scc (len v2)
  | ST_Len : forall t1 t1',
      t1 --> t1' ->
      len t1 --> len t1'
  | ST_IdxZro : forall v1 v2,
      nvalue v1 ->
      lvalue v2 ->
      idx zro (cns v1 v2) --> v1
  | ST_IdxScc : forall v1 v2 v3,
      nvalue v1 ->
      nvalue v2 ->
      lvalue v3 ->
      idx (scc v1) (cns v2 v3) --> idx v1 v3
  | ST_Idx2 : forall v1 t2 t2',
      nvalue v1 ->
      t2 --> t2' ->
      idx v1 t2 --> idx v1 t2'
  | ST_Idx1 : forall t1 t1' t2,
      t1 --> t1' ->
      idx t1 t2 --> idx t1' t2
  | ST_StnNval : forall v1,
      nvalue v1 ->
      stn v1 --> cns v1 nul
  | ST_Stn : forall t1 t1',
      t1 --> t1' ->
      stn t1 --> stn t1'

where "t1 '-->' t2" := (step t1 t2).

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive ty : Type :=
  | Nat : ty
  | List : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Zro :
      |- zro \in Nat
  | T_Scc : forall t1,
      |- t1 \in Nat ->
      |- scc t1 \in Nat
  | T_Pls : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in Nat ->
      |- pls t1 t2 \in Nat
  | T_Nul :
      |- nul \in List
  | T_Cns : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in List ->
      |- cns t1 t2 \in List
  | T_Len : forall t1,
      |- t1 \in List ->
      |- len t1 \in Nat
  | T_Idx : forall t1 t2,
      |- t1 \in Nat ->
      |- t2 \in List ->
      |- idx t1 t2 \in Nat
  | T_Stn : forall t1,
      |- t1 \in Nat ->
      |- stn t1 \in List

where "'|-' t '\in' T" := (has_type t T).

Definition progress := forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

Definition preservation := forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Definition soundness := forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~ stuck t'.
```
```lean
inductive tm : Type
  | zro : tm
  | scc : tm -> tm
  | pls : tm -> tm -> tm
  | nul : tm
  | cns : tm -> tm -> tm
  | len : tm -> tm
  | idx : tm -> tm -> tm
  | stn : tm -> tm
open tm

inductive nvalue : tm -> Prop
  | nv_zro : nvalue zro
  | nv_scc : Π v1, nvalue v1 -> nvalue (scc v1)
open nvalue

inductive lvalue : tm -> Prop
  | lv_nul : lvalue nul
  | lv_cns : Π v1 v2,
      nvalue v1 -> lvalue v2 -> lvalue (cns v1 v2)

def value (t : tm) := nvalue t ∨ lvalue t

inductive step : tm -> tm -> Prop
notation x  ` ⟶ `:100 y := step x y
  | ST_Scc : ∀ t1 t1',
      (t1 ⟶ t1') →
      scc t1 ⟶ scc t1'
  | ST_PlsZro : ∀ v1,
      nvalue v1 →
      pls zro v1 ⟶ v1
  | ST_PlsScc : ∀ v1 v2,
      nvalue v1 →
      nvalue v2 →
      pls (scc v1) v2 ⟶ scc (pls v1 v2)
  | ST_Pls2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      pls v1 t2 ⟶ pls v1 t2'
  | ST_Pls1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      pls t1 t2 ⟶ pls t1' t2
  | ST_Cns2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      cns v1 t2 ⟶ cns v1 t2'
  | ST_Cns1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      cns t1 t2 ⟶ cns t1' t2
  | ST_LenNul :
      len nul ⟶ zro
  | ST_LenCns : ∀ v1 v2,
      nvalue v1 →
      lvalue v2 →
      len (cns v1 v2) ⟶ scc (len v2)
  | ST_Len : ∀ t1 t1',
      (t1 ⟶ t1') →
      len t1 ⟶ len t1'
  | ST_IdxZro : ∀ v1 v2,
      nvalue v1 →
      lvalue v2 →
      idx zro (cns v1 v2) ⟶ v1
  | ST_IdxScc : ∀ v1 v2 v3,
      nvalue v1 →
      nvalue v2 →
      lvalue v3 →
      idx (scc v1) (cns v2 v3) ⟶ idx v1 v3
  | ST_Idx2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      idx v1 t2 ⟶ idx v1 t2'
  | ST_Idx1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      idx t1 t2 ⟶ idx t1' t2
  | ST_StnNval : ∀ v1,
      nvalue v1 →
      stn v1 ⟶ cns v1 nul
  | ST_Stn : ∀ t1 t1',
      (t1 ⟶ t1') →
      stn t1 ⟶ stn t1'
open step

infix ` ⟶ `:100 := step 

def relation (X : Type) := X → X → Prop

def deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

inductive ty : Type
  | Nat : ty 
  | List : ty
open ty

inductive has_type : tm → ty → Prop
notation `⊢ `:79 t ` :∈ `:80 T := has_type t T
  | T_Zro :
      ⊢ zro :∈ Nat 

  | T_Scc : ∀ t1,
      (⊢ t1 :∈ Nat) →
      ⊢ scc t1 :∈ Nat
  | T_Pls : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ Nat) →
      ⊢ pls t1 t2 :∈ Nat

  | T_Nul :
      ⊢ nul :∈ List
  | T_Cns : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ List) →
      ⊢ cns t1 t2 :∈ List

  | T_Len : ∀ t1,
      (⊢ t1 :∈ List) →
      (⊢ len t1 :∈ Nat)
  | T_Idx : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ List) →
      ⊢ idx t1 t2 :∈ Nat
  | T_Stn : ∀ t1,
      (⊢ t1 :∈ Nat) →
      ⊢ stn t1 :∈ List
open has_type

notation `⊢ `:19 t ` :∈ `:20 T := has_type t T

def progress := ∀ t T,
  (⊢ t :∈ T) →
  value t ∨ ∃ t', t ⟶ t'

def preservation := ∀ t t' T,
  (⊢ t :∈ T) →
  t ⟶ t' →
  ⊢ t' :∈ T

inductive multi {X : Type} (R : relation X) : relation X 
  | multi_refl : ∀ (x : X), multi x x
  | multi_step : ∀ (x y z : X),
                    R x y →
                    multi y z →
                    multi x z

def multistep := (multi step).
infix ` ⟶* `:100  := (multistep)

def normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

notation `step_normal_form` := (normal_form step)

def stuck (t : tm) : Prop :=
  step_normal_form t ∧ ¬ value t

def soundness := ∀ t t' T,
  (⊢ t :∈ T) →
  t ⟶* t' →
  ¬ stuck t'

notation `SUBMISSION_DET` := deterministic step
notation `SUBMISSION_PROG` := progress ∨ ¬ progress
notation `SUBMISSION_PRES` := preservation ∨ ¬ preservation
notation `SUBMISSION_SOUND` := soundness ∨ ¬ soundness
```
