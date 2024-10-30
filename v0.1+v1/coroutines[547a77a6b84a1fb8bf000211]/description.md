In this kata we will implement a simple version of coroutines using continuations. Coroutines form the basis for streaming libraries such as [pipes](https://hackage.haskell.org/package/pipes) and to a lesser extent [conduit](https://hackage.haskell.org/package/conduit). 

Perhaps the best way to think about coroutines is in terms of baton passing. A coroutine `y` may decide to run for a while before needing more input to continue. At this point, it passes the baton to `x` which, when it computes the value required by `y`, passes this baton to `y` so that `y` can continue its computation. This abstraction provides a very elegant way to suspend and restart computations. 

We first introduce the `Coroutine` monad. Notice it is very similar to the continuation monad.

```
newtype Coroutine r u d a = Coroutine { runCoroutine :: (Command r u d a -> r) -> r }
```

`Command` is a datatype which we use to indicate the next action we want to take. The semantics of the three constructors are as follows. 

* `Done` indicates that we have finished the computation. 
* `Out` means that we should output a value but then continue the computation. 
* `In` means that we wait for an input to be provided before carrying on the computation.

```
data Command r u d a =
    Done a 
  | Out d (Coroutine r u d a) 
  | In (u -> Coroutine r u d a)
```

A useful operator for working with coroutines is `(>>>) :: Coroutine r u m a -> Coroutine r m d a -> Coroutine r u d a` pronounced pipe. The semantics of `x >>> y` are as follows.

We start by executing `y` normally until `y` requests additional input (by the `In` constructor). At this point we transfer control to `x` which executes normally until it attempts to output (by the `Out` constructor) at which point we resume computation of `y`; the value that `x` produced in its output is used as `y`'s input. If either `x` or `y` terminate with the value `v` then `v` is the value of the whole pipe. 

With this machinery we can then define some basic library functions. 

* `input`: Waits for an input before returning it.
* `output`: Immediately output the argument.
* `produce`: Output each element in a list in order.
* `consume`: Collect all outputted values into a list.
* `filter`: Repeatedly request for input and output it, if it matches a predicate.
* `limit`: Allow `n` items to pass through before terminating (similar to `take` from the prelude).
* `suppress`: Disallow the first `n` items to pass through (similar to `drop` from the prelude).
* `add`: Repeatedly take two inputs and output their sum.
* `duplicate`: Repeatedly receive input and output it twice.

Notice that `add` and `duplicate` should never terminate.

## Programs

Using these library functions we should define several simple programs.

1. A program which outputs the first 5 even numbers of a stream.
2. A program which produces a stream of the triangular numbers, starting with 1.
3. A program which multiplies the items of a stream by 2.
4. A program which sums adjacent pairs of integers.

Note that none of your programs should use `produce`. 

### Examples

```
consume (produce [0..] >>> p1) === [0, 2, 4, 6, 8]

consume p2 === [1, 3, 6, 10, ...]

consume (produce [0..] >>> p3) === [0, 2, 4, 6, 8]

consume (produce [0, 1, 2, 3] >>> p4) === [1,3,5]
```

`
The task is as follows.

1. Show that `Coroutine` gives rise to a Monad.
2. Define the `>>>` operator.
3. Implement the simple library functions.
4. Use the library operators to write some programs.