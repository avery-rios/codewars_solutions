This is the subsequent Kata of [this one](https://www.codewars.com/kata/597ccf7613d879c4cb00000f).

In this Kata you should convert the representation of "type"s, from Kotlin to Java, and **you don't have to know Kotlin or Java in advance** :D

```if:haskell
If you successfully parsed the input, return `Right result`, otherwise give me `Left "Hugh?"`.
```
```if:javascript
If you successfully parsed the input, return the result, otherwise give me `null`.
```
```if:java
If you successfully parsed the input, return the result, otherwise give me `null`.
```
```if:python
If you successfully parsed the input, return the result, otherwise give me `None`.
```


In Kotlin and Java, C-style identifiers are valid `simple type`s. Like, `_A`, `ice1000`, `Voile`.

We can have generic parameters, which are valid in both Kotlin\&Java: `List<String>`, or more than one parameters: `F<A,B>`.

We can specify the complete package name of the types, like `java.util.List<String>`.

We can also have types of nested classes: `List<Long>.Iterator<Long>`.

We have covariance: `Option<out T>` in Kotlin and `Option<? extends T>` in Java (be careful about the spaces, there are spaces between `?` and `extends`, `extends` and `T`).

Contravariance as well: `Maker<in T>` in Kotlin and `Maker<? super T>` in Java (again, spaces).

In Kotlin, there's something called "star projection" like `List<*>`, and you should translate it into `List<?>`.

Also, you should rename `Int`(`kotlin.Int`) into `Integer`(`java.lang.Integer`), and `Unit` into `Void`.

Finally, the most complex part of this Kata -- the types of lambda expressions.

`(A) -> B` in Kotlin, should be transpiled into `Function1<A,B>` in Java (be careful, here we don't have spaces in Java).  
`() -> B` -> `Function0<B>`  
`(A, B) -> C` -> `Function2<A,B,C>`

So let's see the strict bnf definition:

### Kotlin

```bnf
name           ::= <valid java identifier>
typeParam      ::= "*"
                 | "in " type
                 | "out " type
                 | type
typeParams     ::= typeParam [ "," typeParams ]
simpleUserType ::= name [ "<" typeParams ">" ]
userType       ::= simpleUserType [ "." userType ]
parameters     ::= type [ "," parameters ]
functionType   ::= "(" [ parameters ] ")" "->" type
type           ::= functionType
                 | name
                 | userType
```

### Java

```bnf
name           ::= <valid java identifier>
typeParam      ::= type
                 | "?"
                 | "? super " type
                 | "? extends " type
typeParams     ::= typeParam [ "," typeParams ]
simpleUserType ::= name [ "<" params ">" ]
userType       ::= simpleUserType [ "." userType ]
parameters     ::= type [ "," parameters ]
functionType   ::= "Function" ++ (number of parameters) "<" [ parameters "," ] type ">"
type           ::= functionType
                 | name
                 | userType
```

(`++` in bnf means there shouldn't be spaces there)

for more information please see the example tests.

Enjoy!
