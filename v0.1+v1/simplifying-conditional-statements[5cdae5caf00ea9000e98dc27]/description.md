_This Kata is part of a collection of [supplementary exercises for Programming Language Foundations](https://www.codewars.com/collections/supplementary-exercises-for-programming-language-foundations)._

# Simplifying conditional statements

*The key definitions, concepts and notations presented in this Kata are taken directly from the* [Software Foundations](https://softwarefoundations.cis.upenn.edu/current/index.html) *series, an excellent resource for learning Coq.*

## Prerequisites

You will need to be familiar with the content presented in the following chapters of [Logical Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/index.html):

- [Total and Partial Maps (Maps)](https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html)
- [Simple Imperative Programs (Imp)](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html)

Having read [Program Equivalence (Equiv)](https://softwarefoundations.cis.upenn.edu/current/plf-current/Equiv.html) of [Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/current/plf-current/index.html) is a plus but not absolutely necessary.

## Lesson

*If you have already read "Program Equivalence (Equiv)" in "Programming Language Foundations" then you may safely skip this section.*

In "Simple Imperative Programs (Imp)", we studied a simple toy programming language called *Imp* - its components, how to write programs in Imp and reasoning about simple properties of particular Imp programs as well as Imp itself.  In this Kata (and in "Program Equivalence (Equiv)" of "Programming Language Foundations"), we will develop a theory of *program equivalence*.

First of all, what does it mean for two *arithmetic expressions* to be equivalent? Intuitively, evaluating two equivalent arithmetic expressions should yield the same value. Taking state into account, we say that two arithmetic expressions are equivalent if they evaluate to the same value in any state:

```coq
Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.
```

The equivalence of two *boolean expressions* can be defined similarly as follows:

```coq
Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.
```

As for *programs* themselves, two programs are said to be equivalent if they are indistinguishable in terms of their behavior - that is, they either both diverge (i.e. enter some sort of infinite loop) or converge to the same final state given any initial state:

```coq
Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').
```

## Task

Consider the following Imp program:

```
TEST X = 42 THEN
  Y ::= 100;;
  Z ::= 1
ELSE
  Y ::= 0;;
  Z ::= 1
FI
```

After this program is executed, the value of `Y` could either be `100` or `0` depending on the value of `X`. However, no matter which branch of the conditional is taken, the value of `Z` will be set to `1`. Therefore, it is safe to bring the statement `Z ::= 1` out of the conditional statement:

```
TEST X = 42 THEN
  Y ::= 100
ELSE
  Y ::= 0
FI;;
Z ::= 1
```

But is this true *in general*? That is, is it *always* safe to rewrite a conditional of the form:

```
TEST b THEN
  c1;;
  c3
ELSE
  c2;;
  c3
FI
```

into the following?

```
TEST b THEN
  c1
ELSE
  c2
FI;;
c3
```

Your task is to decide whether that is the case and prove your claim.

## Preloaded

The source code of `Preloaded.v` is displayed below for your reference:

```coq
(* Preloaded.v

   The key definitions and notations in this file are taken
   directly from the Software Foundations series, an
   excellent resource for learning Coq:
   https://softwarefoundations.cis.upenn.edu/current/index.html

   The copyright notice of the series is reproduced below as
   follows:

   Copyright (c) 2019

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
   THE SOFTWARE. *)

(* Volume 1: Logical Foundations *)

(* Total and Partial Maps (Maps) *)

Require Export Coq.Strings.String.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

(* Simple Imperative Programs (Imp) *)

Require Import Coq.Arith.PeanoNat.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.
Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Reserved Notation "st '=[' c ']=>' st'" (at level 40).
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st''->
      st =[ WHILE b DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(* Volume 2: Programming Language Foundations *)

(* Program Equivalence (Equiv) *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').
```