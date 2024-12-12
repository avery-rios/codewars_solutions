## A company in a pickle
Your new boss discovered Haskell a few weeks ago and decided that it will be used for the next project.
They like its syntax and strong type system.

The only thing blocking the next project is that it looks like everything in Haskell must be a pure function.

Were did the mutability go? What happened to good old if-statements?

# Your task

Your task is to fix this important issue and unblock your company.

Specifically, we want be able to mutate variables and use if/elif/else statements like the following:

```haskell
fizzBuzz = def do
  result <- var []
  current <- var 1

  while current (<=) 100 do
    if' current isDivisibleBy 15 do
      result `push` "FizzBuzz"

    elif' current isDivisibleBy 3 do
      result `push` "Fizz"

    elif' current isDivisibleBy 5 do
      result `push` "Buzz"

    else' do
      currentAsString <- toString current
      result `push` currentAsString

    current += 1

  return result
```

Additionally, we want the compiler to refuse obviously wrong programs like:
```haskell
invalid1 = def do
    else' do -- invalid else without if
        ...

invalid2 = def do
    if' ... do
        ...
    else' do
        ...
    else' do -- invalid second else
        ...
```

## Remarks

This kata is inspired by [The most imperative functional language?](https://www.codewars.com/kata/5453af58e6c920858d000823), which is similar and also worth a look.