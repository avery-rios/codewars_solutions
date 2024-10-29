The factorial function is defined as follows:
```
0! = 1
n! = 1 * 2 * 3 * 4 * ... * n-2 * n-1 * n
```

Usually, the factorials of large numbers will have trailing zeroes. Your task is to create a function which returns the number of trailing zeroes of `num!` in a given `base`.

Here's two examples to get you started:
```python
(num = 15, base = 10) => 3
# 15! = 1307674368000, which has 3 trailing 0's

(num = 7, base = 2) => 4
# 7! = 5040 = 0b1001110110000, which has 4 trailing 0's
```

Your code should be able to handle some very large numbers.

Note: 
 - `num` >= 0
 - `base` >= 2

HINT: Should you not make any headway after trying a long time, you should try [this kata](https://www.codewars.com/kata/number-of-trailing-zeros-of-n) first.
