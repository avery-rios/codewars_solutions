In the synonymous functional pearl, Wouter Swierstra demonstrates one way to solve the expression problem. This kata will closely follow his exposition.

The expression problem as first stated by Wadler is as follows:

> The goal is to define a data type by cases, where one can add new cases to the data type
and new functions over the data type, without recompiling existing code, and while retaining
static type safety.

Now by example, consider a very simple ADT.

```haskell
data Expr = Lit Int | Add Expr Expr
```

It is very easy to define different interpretations of this datatype, here are just two examples.

```haskell
eval :: Expr -> Int
eval (Lit n) = n
eval (Add e1 e2) = eval e1 + eval e2

pretty :: Expr -> String
pretty (Lit n) = show n
pretty (Add e1 e2) = pretty e1 ++ "+" ++ pretty e2
```

On the other hand, if we wanted to extend `Expr` to include multiplication.

```haskell
data Expr = Lit Int | Add Expr Expr | Mult Expr Expr
```

Then we have to go back add a clause to where the interpreter was originally defined to add a new clause to recognise `Mult`. This could be problematic if `eval` is defined inside a library to which you don't have access.

Simply, Swierstra's solution is instead of defining an evaluation function, we define an evaluation type class. For each constructor which admits a definition for that operator, we define an instance of the type class.

In this kata we will walk through the first section of [Data Type à la Carte](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.101.4131).

This kata was broken, but now it isn't!