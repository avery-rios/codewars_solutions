This is a hard version of <a href = 'http://www.codewars.com/kata/56a1c074f87bc2201200002e'>How many are smaller than me?</a>. If you have troubles solving this one, have a look at the easier kata first.

Write
```javascript
function smaller(arr)
```
```rust
fn smaller(arr: &[i32]) -> Vec<usize>
```
that given an array ```arr```, you have to return the amount of numbers that are smaller than ```arr[i]``` to the right.

For example:
```javascript
smaller([5, 4, 3, 2, 1]) === [4, 3, 2, 1, 0]
smaller([1, 2, 0]) === [1, 1, 0]
```
```rust
smaller(&[5, 4, 3, 2, 1]) == [4, 3, 2, 1, 0];
smaller(&[1, 2, 0]) == [1, 1, 0];
```
~~~if:python
### Note
Your solution will be tested against inputs with up to 120_000 elements
~~~
~~~if:rust
### Note
Your solution will be tested against inputs with up to 150_000 elements
~~~
~~~if:javascript
### Note
Your solution will be tested against inputs with up to 100_000 elements
~~~