In this kata we will explore using singletons to mimic simple dependent typing
in Haskell. The goal is to reimplement common list functions using vectors
indexed by the natural numbers.

Unlike languages such as Agda and Idris, Haskell differentiates between the
term and the type level. This distinction makes proper dependent types impossible but GHC language extensions can be used to partially mimic the effect.

The idea of singletons is to allow the programmer to infer something about the
type level from the term level. To do this, we construct a datatype (`SNat`)
whose type increments in lock-step with the data. For example:

```
*Singletons> :t SZero
SZero :: SNat 'Zero
*Singletons> :t SSucc SZero
SSucc SZero :: SNat ('Succ 'Zero)
```

This correspondence allows the programmer to specify more specific types than
he usually would. The example we will use is indexed vectors - that is, vectors
which are annotated with their length at the type level. Their definition looks very similar to that of lists but with the extra index parameter `n`.

```
data Vec a n where
  VNil :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)
```

Again inspecting the types - we see that applying the `VCons` constructor changes the type of the whole expression.

```
*Singletons> :t VNil
VNil :: Vec a 'Zero
*Singletons> :t VCons () VNil
VCons () VNil :: Vec () ('Succ 'Zero)
```

The final piece of the puzzle are type families. Simply put, type families are functions which act on types. As a result they are quite a bit more restricted than normal functions but we can use them to perform basic calculations at the type level.

For example the type family `:<` corresponds to the term level operator `<`. It is defined as follows.

```
type family (a :: Nat) :< (b :: Nat) :: Bool
type instance m :< Zero = False
type instance Zero :< Succ n = True
type instance (Succ m) :< (Succ n) = m :< n
```

It will be necessary to define two more type families to complete the kata.

Putting this all together, this is how we might define a safe `index` function.

```
index :: ((a :< b) ~ True) => SNat a -> Vec s b -> s
index SZero (VCons v _) = v
index (SSucc n) (VCons _ xs) = index n xs
```

Your task is to define some common functions which act on lists on an indexed vector. These functions are `map`, `zipWith`, `replicate`, `take`, `drop`, `head`, `tail`, `index` and `++`.

This description has been quite terse. Here are some more links which take a bit more time to explain the concept.

- [Brent Yorgey's explanation](https://byorgey.wordpress.com/2010/07/06/typed-type-level-programming-in-haskell-part-ii-type-families/)
- [Dependently Typed Programming with Singletons](http://www.cis.upenn.edu/~eir/papers/2012/singletons/paper.pdf)
- [GHC wiki page](https://www.haskell.org/haskellwiki/GHC/Type_families)

HINT: You may find defining a type family corresponding to subtraction useful.
HINT: You may find definining a type family corresponding to `min` useful.

---

Note: Various `unsafe` operations in Haskell has been banned.