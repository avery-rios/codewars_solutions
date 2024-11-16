## Introduction

This is the same task as the [bisimulation in Idris](https://www.codewars.com/kata/tear-me-apart-and-merge-the-pieces-together) and [in Agda](https://www.codewars.com/kata/pattern-in-the-mirror-and-bisimulation-for-real/agda). You'll be doing it in Coq this time. I decided to make this the third (!) separate kata, since the code you'll write is totally different from the other two.

## Coinduction in Coq

In Coq, **coinductive datatypes** represent possibly infinite structures. They are defined just like inductive datatypes, except that they use `CoInductive` keyword instead.

```coq
CoInductive stream (A : Set) : Set :=
  | cons : A -> stream A -> stream A.
Arguments cons {_} hd tl.

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Definition head {A} (x : stream A) := match x with
  hd :: _ => hd end.
Definition tail {A} (x : stream A) := match x with
  _ :: tl => tl end.
```

## Co-recursive definition in Coq (CoFixpoint)

As a dual of `Fixpoint` definition, Coq provides `CoFixpoint` keyword for infinitely productive definitions. While `Fixpoint` expects `Inductive` arguments to be structurally decreasing, `CoFixpoint` expects `CoInductive` *result* to be structurally *productive*; that is, the result should provide any finite parts of it in finite time.

For example, the following is a good definition of an infinite stream of ones:

```coq
CoFixpoint ones : stream nat := 1 :: ones.
```

The following is a bad corecursive definition.

```coq
CoFixpoint what : stream nat := what.
```

Coq complains that the recursive call is not guarded. *Guardedness* is how Coq checks that a definition is productive. Basically, it says that **co-recursive call must be a direct argument to a constructor, nested only inside of other constructor calls or fun or match expressions**. In order to see this, look at the following:

```coq
CoFixpoint what2 : stream nat := tail (1 :: what2).
```

Even though `what2` appears in a constructor, the outer function `tail` strips it off, making it essentially the same as `what`.

## Co-recursive proof in Coq (cofix tactic)

We can't prove two infinite streams are equal by `=`; instead, we define *bisimulation* to represent equality of two streams.

```coq
CoInductive bisim {A : Set} (x y : stream A) : Set :=
  | bisim_eq : head x = head y -> bisim (tail x) (tail y) -> bisim x y.
Notation "x == y" := (bisim x y) (at level 70).
```

Since the type `bisim` is coinductive, the proof to a theorem of type `bisim x y` should be corecursive. Let's prove reflexivity as an example.

```coq
Theorem bisim_refl : forall {A : Set} (a : stream A), a == a.
Proof.

1 subgoal
______________________________________(1/1)
forall (A : Set) (a : stream A), a == a
```

The `cofix` tactic introduces a hypothesis that is exactly the same type as the goal. (CIH is for Co-Inductive Hypothesis.)

```coq
cofix CIH.

1 subgoal
CIH : forall (A : Set) (a : stream A), a == a
______________________________________(1/1)
forall (A : Set) (a : stream A), a == a
```

Using `auto` will close the goal immediately using `CIH`, but when you write `Qed.`, Coq will complain that the definition is not guarded.

The correct step is to dissect the goal as usual, apply a constructor (one or more times), and then close it with `CIH`.

```coq
intros A a. (* Just like what you do with usual proofs. *)

1 subgoal
CIH : forall (A : Set) (a : stream A), a == a
A : Set
a : stream A
______________________________________(1/1)
a == a

constructor. (* This will dissect into equality of heads / bisimulation of tails. *)

2 subgoals
CIH : forall (A : Set) (a : stream A), a == a
A : Set
a : stream A
______________________________________(1/2)
head a = head a
______________________________________(2/2)
tail a == tail a

reflexivity. (* Heads part is easy. *)

1 subgoal
CIH : forall (A : Set) (a : stream A), a == a
A : Set
a : stream A
______________________________________(1/1)
tail a == tail a

apply CIH. (* Now we can close the proof. *)

No more subgoals.

Qed.
```

We can confirm that the generated proof is guarded by printing it:

```coq
Print bisim_refl.

bisim_refl = 
cofix CIH (A : Set) (a : stream A) : a == a := bisim_eq a a eq_refl (CIH A (tail a))
     : forall (A : Set) (a : stream A), a == a
```

The `CIH` call is guarded with one layer of `bisim_eq` and nothing else.

One problem with `cofix`, especially when doing interactive proof, is that the guardedness check is done at `Qed.` (or `Defined.`) only. To mitigate this, Coq provides a top-level command `Guarded.` to check guardedness anywhere in the proof. Use it whenever you're not sure.

### Problem with unfolding cofixpoint functions

Cofixpoint definitions are unfolded *only* when the next part (constructor) is requested by `match .. with`. In proofs, this means that `simpl` and similar tactics don't unfold the definitions by default. We need a seemingly dumb lemma to manually unfold them:

```coq
Lemma stream_unfold : forall {A : Set} (a : stream A), a = head a :: tail a.
Proof. intros A a. destruct a. reflexivity. Qed.
```

When you rewrite with this lemma *outside* the offending function using e.g.

```coq
rewrite (stream_unfold (merge _ _)); simpl.
```

then the `merge` call will correctly unfold once.

### Problem with cofix and rewrite-at

`rewrite .. at n` tactic is good for rewriting the goal selectively. Unfortunately, it creates unguarded proofs in `cofix` context. Instead, you can use the following:

```coq
(* instead of writing this *)
rewrite (x : a = b) at n.
(* write this *)
pattern (a) at n; rewrite x.
```

The details behind this, and more in-depth guides about `cofix`, can be found in [this article](http://adam.chlipala.net/cpdt/html/Coinductive.html).