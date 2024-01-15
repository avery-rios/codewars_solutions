Motivation
---------
The goal of data compression is to remove redundancy from an input. Some of you already know run-length-encoding, where elements get encoded with their number of consecutive occurences. But what if elements are not directly consecutive but just close to each other?

(This is especially important for the Burrows-Wheeler-Transformation, which creates a permutation of the input, where equal symbols are close to each other. There is also a [kata](http://www.codewars.com/kata/burrows-wheeler-transformation/) about that from me.)

Move To Front Encoding
--------------------
In this encoding we use a prioritized and changing alphabet for our input. As the name suggests, when encoding a symbol from our alphabet, we look up the index of that symbol in our alphabet. This is our representation for that symbol, and then change the alphabet, by moving the symbol to the front. Example with the alphabet `['a', 'b', 'c']`:
```haskell
encode "abc" "ccc"    == Just [2, 0, 0]
encode "abc" "acacac" == Just [0, 2, 1, 1, 1, 1]
encode "aab" "b"      == Just [2]
```
```javascript
encode("abc", "ccc")    === [2, 0, 0]
encode("abc", "acacac") === [0, 2, 1, 1, 1, 1]
encode("aab", "b")      === [2]
```
As you can see the numbers get smaller the more often symbols occur in proximity, and smaller numbers can be represented in less space.

Decoding works in the exact same direction, just that we look up the index in the alphabet, instead of the actual element.

Goal
----
Write `encode` and `decode` for the Move-To-Front-Encoding.
```if:haskell
Note: Both can fail, and alphabets can be infinite in size!
```
```if:javascript
Return `null` if encoding or decoding fails.  
Also note alphabets can have repeating characters, and can be quite large.  
The alphabet may be an Array of Numbers or a String; `encode`'s second argument will be this same type, and `decode`'s return value must be this same type.  
Inputs must not be modified.
```