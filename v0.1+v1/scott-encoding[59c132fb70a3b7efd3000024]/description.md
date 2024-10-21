Can you make algebraic data types even more functional? Of course!

Scott encoding represents data as funtion that apply their argument (also a function) to their value. This approach is similar to using pattern matching on regular ADTs to extract and use their content.

```if:haskell
You are given types representing the Scott encoding of four common Haskell types: Maybe, lists, Either and pairs (2-tuples). 
```
```if:scala
You are given types representing the Scott encoding of four common Scala types: Option, List, Either and Tuple. 
```
Your task is to implement conversion functions between these regular types and their Scott encoding.

In addition, you will have to implement the following common operations using the provided Scott-encoded data types:
- `fst` and `snd`, functions to extract the content of a pair
- `swap`, a function that exchanges the content of a pair
- `curry`, a function to turn functions of pairs into functions of two arguments
- `uncurry`, a function to turn functions of two arguments into functions of pairs

```if:haskell
- `isJust` and `isNothing`, predicates testing wether a Maybe contains data
```
```if:scala
- `isSome` and `isNone`, predicates testing wether a Option contains data
```
- `isLeft` and `isRight`, predicates testing which side is contained in an Either
- `cons`, a function to prepend an element to a list
- `concat`, a function to contanetate two lists

```if:haskell
- `catMaybes`, a function to flatten a list of Maybes by removing Nothings
```
```if:scala
- `catOptions`, a function to flatten a list of Options by removing Nones
```

```if:haskell
- `null`, a predicate testing wether a list is empty
```
```if:scala
- `empty`, a predicate testing wether a list is empty
```
- `length`, a function returning the number of elements in a list
- `map`, a function to transform the contents of a list according to a given function
- `zip`, a funtion to merge two lists into a list of pairs
- `partition`, a function that splits a list of Eithers in a pair of Lefts and Rights

```if:haskell
- `foldl` and `foldr`,  functions to reduce a list to a single value by successive application of a given function
```
```if:scala
- `foldLeft` and `foldRight`,  functions to reduce a list to a single value by successive application of a given function
```
- `take`, a function to limit a list to a number of initial elements