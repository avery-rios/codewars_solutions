Write a function which makes a list of strings representing all of the ways you can balance `n` pairs of parentheses

### Examples

```haskell
balancedParens 0 -> [""]
balancedParens 1 -> ["()"]
balancedParens 2 -> ["()()","(())"]
balancedParens 3 -> ["()()()","(())()","()(())","(()())","((()))"]
```
```javascript
balancedParens(0) => [""]
balancedParens(1) => ["()"]
balancedParens(2) => ["()()","(())"]
balancedParens(3) => ["()()()","(())()","()(())","(()())","((()))"]
```
```java
balancedParens(0) returns ArrayList<String> with element:  ""
balancedParens(1) returns ArrayList<String> with element:  "()"
balancedParens(2) returns ArrayList<String> with elements: "()()","(())"
balancedParens(3) returns ArrayList<String> with elements: "()()()","(())()","()(())","(()())","((()))"
```
```ruby
balanced_parens(0) => [""]
balanced_parens(1) => ["()"]
balanced_parens(2) => ["()()","(())"]
balanced_parens(3) => ["()()()","(())()","()(())","(()())","((()))"]
```
```python
balanced_parens(0) => [""]
balanced_parens(1) => ["()"]
balanced_parens(2) => ["()()","(())"]
balanced_parens(3) => ["()()()","(())()","()(())","(()())","((()))"]
```
```csharp
BalancedParens(0) returns List<string> with element:  ""
BalancedParens(1) returns List<string> with element:  "()"
BalancedParens(2) returns List<string> with elements: "()()","(())"
BalancedParens(3) returns List<string> with elements: "()()()","(())()","()(())","(()())","((()))"
```
```elixir
balanced_parens(0) => [""]
balanced_parens(1) => ["()"]
balanced_parens(2) => ["()()","(())"]
balanced_parens(3) => ["()()()","(())()","()(())","(()())","((()))"]
```
```julia
balancedParens(0) --> [""]
balancedParens(1) --> ["()"]
balancedParens(2) --> ["()()","(())"]
balancedParens(3) --> ["()()()","(())()","()(())","(()())","((()))"]
```