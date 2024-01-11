Write a simple parser that will parse and run Deadfish.  

Deadfish has 4 commands, each 1 character long:
* `i` increments the value (initially `0`)
* `d` decrements the value
* `s` squares the value
* `o` outputs the value into the return array

Invalid characters should be ignored.

```javascript
parse("iiisdoso") => [ 8, 64 ]
```
```csharp
Deadfish.Parse("iiisdoso") => new int[] {8, 64};
```
```python
parse("iiisdoso")  ==>  [8, 64]
```
```haskell
parse "iiisdoso" -> [ 8, 64 ]
```
```c
parse("iiisdoso") == {8, 64}
```
```go
Parse("iiisdoso") == []int{8, 64}
```
```ruby
parse("iiisdoso")  ==>  [8, 64]
```
```java
Deadfish.parse("iiisdoso") =- new int[] {8, 64};
```
```groovy
DeadFish.parse("iiisdoso")  ==>  [8, 64]
```
```scala
Deadfish.parse("iiisdoso") => List(8, 64)
```
```typescript
parse("iiisdoso") => [8, 64]
```
```julia
deadfish("iiisdoso") --> [8, 64]
```
```powershell
Eval-DeadFish -Data "ooo" --> @(0, 0, 0)  # [long[]]

```
```factor
"iiisdoso" deadfish -> { 8 64 }
```
