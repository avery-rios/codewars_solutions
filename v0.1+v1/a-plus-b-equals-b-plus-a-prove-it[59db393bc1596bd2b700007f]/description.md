_Note to translators: This Kata is **NOT** accepting any translations to Coq / Idris / Agda / Lean due to the huge difference in difficulty between Haskell and those languages mentioned. Any translations violating this rule will be rejected without further reason._

-----

_**Before you begin!** This kata is intended as a successor to the kata [Even + Odd = Odd? Prove it!][previous] If you haven't completed it, you will find this kata very difficult._

-----

  # What's this kata about?
In this kata, you will prove the commutativity of addition, that is to say, the fact that `a + b = b + a`. Specifically you will be proving it for the natural numbers.

-----

  # What can I use?
You have three useful datastructures defined for you in the module `Kata.AdditionCommutes.Definitions`. You are given no more help in creating this proof.

### The natural numbers
This is a very simple definition of the natural numbers, using types.

    data Z
    data S n

### The 'Natural' type

This can be thought of as a predicate, meaning that some number n is a natural number. This is useful for passing numbers to our proofs.
 
    data Natural :: * -> * where
      NumZ :: Natural Z
      NumS :: Natural n -> Natural (S n)

### The 'Equal' type
This is a statement of equality on natural numbers.

    data Equal :: * -> * -> * where
        EqlZ :: Equal Z Z
        EqlS :: Equal n m -> Equal (S n) (S m)

### The addition type family
This is Peano's description of addition.

    type family (:+:) (n :: *) (m :: *) :: *
    type instance Z :+: m = m
    type instance S n :+: m = S (n :+: m)

-----

  # What's the final goal?
You must write a proof, ie: a function, as so:

    plusCommutes :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a) 
    
This will be tested for cheats, ie: using `undefined` instead of the actual proof.

-----

  # What problems might I have?
The challenge of this kata is getting the proof to typecheck. As such, most of the errors produced will be type errors. Cheating or trying to change the names of the types will cause issues. Using `undefined` will very likely cause a problem, too.

Additionally, performance is a serious concern. The tests will take only a few milliseconds to run, but the compilation will take quite a bit of time. Please pay attention to the time it takes to run your tests.

-----
# Good luck!

[previous]: https://www.codewars.com/kata/599d973255342a0ce400009b