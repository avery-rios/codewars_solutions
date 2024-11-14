Say we have a function of this type:
```haskell
f :: Ord a => a -> Either b ([a], [b] -> b)
```
any recursive function of one argument can be implemented in such a way that it fits this type signature - provided with an argument it returns either the result (Left-case) or a pair of new arguments for the function and a function to fold the results (Right-case). For example
```haskell
factorial i | i == 0    = Left 1
            | otherwise = Right ([i-1], (*i).head) 

fibonacci i | i < 2     = Left i
            | otherwise = Right ([i-1, i-2], sum)
```
gives us the usual factorial and Fibonacci functions (for more examples, see the test cases).
## Task

Your task is to write an evaluator for such functions, i.e a function
```haskell
evaluateFunction :: Ord a => (a -> Either b ([a], [b] -> b)) -> a -> b
```
that takes a function of a previously described form and turns it into a simple a -> b function (again, see examples in the test cases).