# Motivation

You've probably seen the advocate that Haskell is the most imperative functional language in this [Kata](https://www.codewars.com/kata/5453af58e6c920858d000823). You know what, as a multi-paradigm language, Haskell is also a most OO functional language, most mutable immutable language, most non-deterministic deterministic language, so on and so on! Specifically, here we are to demonstrate, Haskell is also the most untyped typed language! For those of you who don't know what Haskell is, Haskell is a popular dialect of Church's original untyped lambda calculus (UTLC).

# Task

Your task is to write a domain-specific language (DSL) with support for `app` and `lam` with the following type signature:

```haskell
app :: D -> D -> D
lam :: (D -> D) -> D
```

With this two atomic operations then, we can write a bunch of untyped lambda calculus stuffs like what follows:

```haskell
zero :: D
suc :: D
one :: D
plus :: D
```
Finally, since in Church's formulation of UTLC, there is no support for `pretty-print` and things like that, so we also really need to show that what we achieve is actually the same thing!

# Hints and Acknowledgement

The solution uses recursive types, and is inspired by the well-known textbook *Types and Programming Languages*. Feel free to use `error` when the execution is supposed to get stuck.