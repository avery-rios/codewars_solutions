_Note to translators: This Kata is **NOT** accepting any translations to Coq / Agda / Lean due to the huge difference in difficulty between Haskell and those languages mentioned. Any translations violating this rule will be rejected without further reason._

***

_**Looking for a challenge?** The kata [A+B=B+A? Prove it!](https://www.codewars.com/kata/59db393bc1596bd2b700007f) is a great next step to this kata._
-----

# What's this kata about?

In this kata, you will prove, via types multiple facts about even and odd numbers. These facts include:

- If *n* is even, then *n+1* is odd.
- If *n* is odd, then *n+1* is even.
- If *n* is even and *m* is odd, then *n+m* is odd.

...and so on.

**This will require knowledge of type families, datakinds, and GADTs.**

# How do we prove something with types?

Functions can be read as implications. Think of the type `A -> B` as reading 'if we have an `A`, then we can get a `B`'. For this reason, if we think of types as propositions rather than data, then we can build proofs using functions between them, where `A -> B` is read as '`A` implies `B`'.

In this kata, three datatypes are defined:

```haskell
-- | The natural numbers.
data Nat = Z | S Nat

-- | The axioms of the even numbers.
data Even (n :: Nat) where
  -- | Axiom: zero is even.
  ZeroEven :: Even Z
  -- | Axiom: if n is even, then n+2 is even.
  NextEven :: Even n -> Even (S (S n))

-- | The axioms of the odd numbers.
data Odd (n :: Nat) where
  -- | Axiom: one is odd.
  OneOdd :: Odd (S Z)
  -- | Axiom: if n is odd, then n+2 is odd.
  NextOdd :: Odd n -> Odd (S (S n))
```
```idris
public export
data Even : Nat -> Type where
  -- | Zero is even.
  ZeroEven : Even Z
  -- | If n is even, then n+2 is even.
  NextEven : Even n -> Even (S (S n))

public export
data Odd : Nat -> Type where
  -- | One is odd.
  OneOdd : Odd (S Z)
  -- | If n is odd, then n+2 is odd.
  NextOdd : Odd n -> Odd (S (S n))
```

Now we have the *axioms* built. Here they are represented as data constructors, but in the corresponding proof we can imagine them as the base assumptions from which we can build our proofs.

Once we have type families for certain operations built, we can build proofs like so:

```haskell
evenPlusOdd :: Even n -> Odd m -> Odd (Add m n)
evenPlusOdd = -- (proof here)
```
```idris
evenPlusOdd : Even n -> Odd m -> Odd (m + n)
evenPlusOdd = ?proof
```

The initial solution will provide type signatures for all the proofs you will need to complete. Good luck!

(Remember: the principle challenge in this kata is getting it to typecheck. The rest is easy, as long as you don't use `undefined`.)