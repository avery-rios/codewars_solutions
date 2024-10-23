# How many ways can you make the sum of a number?

From wikipedia: https://en.wikipedia.org/wiki/Partition_(number_theory)

>In number theory and combinatorics, a partition of a positive integer *n*, also called an *integer partition*, is a way of writing n as a sum of positive integers. Two sums that differ only in the order of their summands are considered the same partition. If order matters, the sum becomes a composition. For example, 4 can be partitioned in five distinct ways:
```
4
3 + 1
2 + 2
2 + 1 + 1
1 + 1 + 1 + 1
```

## Examples

### Basic

```javascript
sum(1) // 1
sum(2) // 2  -> 1+1 , 2
sum(3) // 3 -> 1+1+1, 1+2, 3
sum(4) // 5 -> 1+1+1+1, 1+1+2, 1+3, 2+2, 4
sum(5) // 7 -> 1+1+1+1+1, 1+1+1+2, 1+1+3, 1+2+2, 1+4, 5, 2+3

sum(10) // 42
```
```haskell
explosiveSum  1   -- 1
explosiveSum 2   -- 2 -> 1+1 , 2
explosiveSum 3   -- 3 -> 1+1+1, 1+2, 3
explosiveSum 4   -- 5 -> 1+1+1+1, 1+1+2, 1+3, 2+2, 4
explosiveSum 5   -- 7 -> 1+1+1+1+1, 1+1+1+2, 1+1+3, 1+2+2, 1+4, 5, 2+3

explosiveSum 10  -- 42
```
```ruby
exp_sum(1) # 1
exp_sum(2) # 2  -> 1+1 , 2
exp_sum(3) # 3 -> 1+1+1, 1+2, 3
exp_sum(4) # 5 -> 1+1+1+1, 1+1+2, 1+3, 2+2, 4
exp_sum(5) # 7 -> 1+1+1+1+1, 1+1+1+2, 1+1+3, 1+2+2, 1+4, 5, 2+3

exp_sum(10) # 42
```
```python
exp_sum(1) # 1
exp_sum(2) # 2  -> 1+1 , 2
exp_sum(3) # 3 -> 1+1+1, 1+2, 3
exp_sum(4) # 5 -> 1+1+1+1, 1+1+2, 1+3, 2+2, 4
exp_sum(5) # 7 -> 1+1+1+1+1, 1+1+1+2, 1+1+3, 1+2+2, 1+4, 5, 2+3

exp_sum(10) # 42
```
```cpp
exp_sum(1) // 1
exp_sum(2) // 2  -> 1+1 , 2
exp_sum(3) // 3 -> 1+1+1, 1+2, 3
exp_sum(4) // 5 -> 1+1+1+1, 1+1+2, 1+3, 2+2, 4
exp_sum(5) // 7 -> 1+1+1+1+1, 1+1+1+2, 1+1+3, 1+2+2, 1+4, 5, 2+3

exp_sum(10) // 42
```
```go
ExpSum(1) // 1
ExpSum(2) // 2 -> 1+1 , 2
ExpSum(3) // 3 -> 1+1+1, 1+2, 3
ExpSum(4) // 5 -> 1+1+1+1, 1+1+2, 1+3, 2+2, 4
ExpSum(5) // 7 -> 1+1+1+1+1, 1+1+1+2, 1+1+3, 1+2+2, 1+4, 5, 2+3

ExpSum(10) // 42
```
```rust
exp_sum(1) // 1
exp_sum(2) // 2  -> 1+1 , 2
exp_sum(3) // 3 -> 1+1+1, 1+2, 3
exp_sum(4) // 5 -> 1+1+1+1, 1+1+2, 1+3, 2+2, 4
exp_sum(5) // 7 -> 1+1+1+1+1, 1+1+1+2, 1+1+3, 1+2+2, 1+4, 5, 2+3

exp_sum(10) // 42
```

### Explosive

```javascript
sum(50) // 204226
sum(80) // 15796476
sum(100) // 190569292
```
```haskell
explosiveSum  50 --    204226
explosiveSum  80 --  15796476
explosiveSum 100 -- 190569292
```
```ruby
exp_sum(50) # 204226
exp_sum(80) # 15796476
exp_sum(100) # 190569292
```
```python
exp_sum(50) # 204226
exp_sum(80) # 15796476
exp_sum(100) # 190569292
```
```cpp
exp_sum(50) // 204226
exp_sum(80) // 15796476
exp_sum(100) // 190569292
```
```go
ExpSum(50) // 204226
ExpSum(80) // 15796476
ExpSum(100) // 190569292
```
```rust
exp_sum(50) // 204226
exp_sum(80) // 15796476
exp_sum(100) // 190569292
```

See [here](http://www.numericana.com/data/partition.htm) for more examples.
