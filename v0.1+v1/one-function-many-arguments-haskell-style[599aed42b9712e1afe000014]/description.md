In this kata, you must write three reasonably simple **polyvariadic functions** in Haskell.

---

# What's a polyvariadic function?

A polyvariadic function is one that may take various numbers of arguments. In this case, any number of arguments. There are various ways of doing this, but here's an example of how the polvariadic functions in this kata will work:

```Haskell
λ> polyAdd 1 3 5 7 9 :: Int
25
λ> polyAdd 1 2 3 :: Int
6
```

---
# What functions must I make?

You must create the following functions:

## polyAdd: adds its arguments together.

```Haskell
λ> polyAdd 1 3 5 7 9 :: Int
25
λ> polyAdd 1 2 3 :: Int
6
```

This will only be given `Int`s, never `Integer`s or `Float`s, etc.

## polyWords: joins its arguments into a spaced string.

```Haskell
λ> polyWords "This" "is" "a" "sentence." :: String
"This is a sentence."
λ> polyWords "Hello," "World!" :: String
"Hello, World!"
```

This is mostly self explanatory. Again, the return type will always be specified. Don't worry too much about edge cases, they will be avoided.

## polyList: groups its arguments into a list.
```Haskell
λ> polyList 5 4 3 2 1 :: [Integer]
[5,4,3,2,1]
λ> polyList 'H' 'e' 'l' 'l' 'o' :: String
"Hello"
```

This must be polymorphic in its arguments. The return type will always be specified.

There are more examples for each of these functions in the example test cases.

---

# I'm stuck. What should I do? (Hints)

## Where should I even start?

Making typeclasses is a good place to start: Since `polyX` could either return a function or a result, you need to make a class including both cases.

## My polyAdd function doesn't realise it's getting Ints.

There's a [constraint trick](http://chrisdone.com/posts/haskell-constraint-trick) that might help you.

## I can't get my polyList function to be polymorphic.

Functional dependencies may help you.