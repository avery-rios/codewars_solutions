In this kata you should do three tasks:

0. evaluate some lisp expressions
0. implement some functions by yourself
0. pretty print lisp expressions (within one line, spaces seperated)

They're very simple.

We have types:

```haskell
data AST = I32 Int       -- numbers
         | Sym String    -- symbols
         | Nul           -- nulls
         | Lst [AST]     -- lists
         | Boo Bool      -- booleans
         | Err           -- errors
         | Nod AST [AST] -- nodes
         deriving (Eq, Show)
--
```

Numbers(`I32`) are 10-based. You don't have to parse hex, oct, or bin.

Symbols(`Sym`) are similiar to C symbols, beginning with `noneOf $ " ,\n\t\r()" ++ [ '0' .. '9' ]`, followed by `noneOf " ,\n\t\r()"`, and `null`, `true`, `false` are not symbols.

Nulls(`Nul`) are `null`s and empty brackets(`()`).

Booleans(`Boo`) are `true`s or `false`s.

Lists(`Lst`) doesn't have literals, they're runtimely constructed.

Nodes(`Nod`) are AST nodes.

Errors(`Err`), when something goes wrong(like unknown functions invoked, or type mismatch)

# Parsers

`,\r\n\t ` are treated as whitespaces(token seperator).

```ebnf
nodes    ::= "(" expr expr* ")"
nulls    ::= "(" ")"
           | "null"
booleans ::= "true"
           | "false"
expr     ::= symbols
           | numbers
           | booleans
           | nulls
           | nodes
```

# Example

## Evaluation

In expression:

```lisp
(+ 1 1)
```

This is a `Nod "+" [I32 1, I32 1]`.

If we have function `+` that sum up the parameters, the result of this Node is `2`.

Sometimes we can define `+` differently. If it's a function that returns the first parameter(sounds weired but it's possible), the result will be `1`.

## Prelude functions

`(+ a b c d)` should be `a + b + c + d`.  
`(- a b c d)` should be `a - b - c - d`.  
`(* a b c d)` should be `a * b * c * d`.  
`(/ a b c d)` should be `a / b / c / d`.  
`(^ a b)` should be `a ^ b`.  
`(> a b)` should be `a > b`.  
`(! true)` should be `false`.  
`(list 1 2 3)` should be `Lst [I32 1, I32 2, I32 3]`.  
`reserse` should reverse the list, `size` should return the length of the list.  
`(.. 1 100)` should be `Lst [I32 1, I32 2, .. I32 100]`.  
`(if a b c)` should be `if a then b else c`. If `c` is not given(`(if a b)`) and `a` is false, return `Nul`.


## Pretty

All expressions should be like:

```lisp
(a (e f g) c)
| | |
| | no spaces between brackets and expressions
| |
| spaces between each two expressions
|
no spaces at beginning or ending
```

Say, `(+     1   (*  2 122)  1)` should be `(+ 1 (* 2 122) 1)`.

For more examples please refer to the sample tests.

`null`, `true`, `false` should be printed as `null`, `true`, `false`.
