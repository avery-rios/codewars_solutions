Your task is to implement a simple regular expression parser. We will have a parser that outputs the following AST of a regular expression:

```haskell
data RegExp = Normal Char       -- ^ A character that is not in "()*|."
            | Any               -- ^ Any character
            | ZeroOrMore RegExp -- ^ Zero or more occurances of the same regexp
            | Or RegExp RegExp  -- ^ A choice between 2 regexps
            | Str [RegExp]      -- ^ A sequence of regexps.
```
```c
RegExp* normal (char);                    // ^ A character that is not in "()*|."
RegExp* any ();                           // ^ Any character
RegExp* zeroOrMore (RegExp *starred);     // ^ Zero or more occurances of the same regexp
RegExp* or (RegExp* left, RegExp* right); // ^ A choice between 2 regexps
RegExp* str (RegExp *first);              // ^ A sequence of regexps, first element
RegExp* add (RegExp *str, RegExp* next);  // ^ A sequence of regexps, additional element
```
```csharp
Reg.Exp normal (char);                    // ^ A character that is not in "()*|."
Reg.Exp any ();                           // ^ Any character
Reg.Exp zeroOrMore (Reg.Exp starred);     // ^ Zero or more occurances of the same regexp
Reg.Exp or (Reg.Exp left, Reg.Exp right); // ^ A choice between 2 regexps
Reg.Exp str (Reg.Exp first);              // ^ A sequence of regexps, first element
Reg.Exp add (Reg.Exp str, Reg.Exp next);  // ^ A sequence of regexps, additional element
```
```cpp
RegExp* normal (char);                     // ^ A character that is not in "()*|."
RegExp* any ();                            // ^ Any character
RegExp* zeroOrMore (RegExp *starred);      // ^ Zero or more occurances of the same regexp
RegExp* orr (RegExp* left, RegExp* right); // ^ A choice between 2 regexps
RegExp* str (RegExp *first);               // ^ A sequence of regexps, first element
RegExp* add (RegExp *str, RegExp* next);   // ^ A sequence of regexps, additional element
```
```python
Normal(c)           # ^ A character (string) that is not in "()*|."
Any()               # ^ Any character
ZeroOrMore(regexp)  # ^ Zero or more occurances of the same regexp
Or(regexp, regexp)  # ^ A choice between 2 regexps
Str([regexps])      # ^ A sequence of regexps.
```
```java
new Void()                            // An empty RegExp object, used only
                                      // as default output for wrong inputs.
new Normal(char c)                    // A character (string) that is not in "()*|."
new Any()                             // Any character
new ZeroOrMore(RegExp regexp)         // Zero or more occurances of the same regexp
new Or(RegExp r1, RegExp r2)          // A choice between 2 regexps
new Str(List<RegExp> lstRegexps])     // A sequence of regexps.

// All these objects implement the toString(), hashCode() and equals() methods and extend the RegExp abstract class.
In addition, you can use the getType() method to obtain a string representing the structure of the object and its children (using Str, Or, Normal, ... dnominations).
```
```javascript
new Normal(c)          // A character that is not in "()*|."
new Any()              // Any character
new ZeroOrMore(regexp) // Zero or more occurances of the same regexp
new Or(regexp,regexp)  // A choice between 2 regexps
new Str([regexp])      // A sequence of regexps
```

As with the usual regular expressions, `Any` is denoted by the `'.'` character, `ZeroOrMore` is denoted by a subsequent `'*'` and `Or` is denoted by `'|'`. Brackets, `(` and `)`, are allowed to group a sequence of regular expressions into the `Str` object.

`Or` is not associative, so `"a|(a|a)"` and `"(a|a)|a"` are both valid regular expressions, whereas `"a|a|a"` is not.

Operator precedences from highest to lowest are: `*`, sequencing and `|`. Therefore the followings hold:

```haskell
"ab*"     -> Str [Normal 'a', ZeroOrMore (Normal 'b')]
"(ab)*"   -> ZeroOrMore (Str [Normal 'a', Normal 'b'])
"ab|a"    -> Or (Str [Normal 'a',Normal 'b']) (Normal 'a')
"a(b|a)"  -> Str [Normal 'a',Or (Normal 'b') (Normal 'a')]
"a|b*"    -> Or (Normal 'a') (ZeroOrMore (Normal 'b'))
"(a|b)*"  -> ZeroOrMore (Or (Normal 'a') (Normal 'b'))
```
```c
"ab*"     -> add (str (normal ('a')), zeroOrMore (normal ('b')))
"(ab)*"   -> zeroOrMore (add (str (normal ('a')), normal ('b')))
"ab|a"    -> or (add (str (normal ('a')), normal ('b')), normal ('a'))
"a(b|a)"  -> add (str (normal ('a')), or (normal ('b'), normal ('a')))
"a|b*"    -> or (normal ('a'), zeroOrMore (normal ('b')))
"(a|b)*"  -> zeroOrMore (or (normal ('a'), normal ('b')))
```
```csharp
"ab*"     -> Reg.add (Reg.str (Reg.normal ('a')), Reg.zeroOrMore (Reg.normal ('b')))
"(ab)*"   -> Reg.zeroOrMore (Reg.add (str (Reg.normal ('a')), Reg.normal ('b')))
"ab|a"    -> Reg.or (Reg.add (Reg.str (Reg.normal ('a')), Reg.normal ('b')), Reg.normal ('a'))
"a(b|a)"  -> Reg.add (Reg.str (Reg.normal ('a')), Reg.or (Reg.normal ('b'), Reg.normal ('a')))
"a|b*"    -> Reg.or (Reg.normal ('a'), Reg.zeroOrMore (Reg.normal ('b')))
"(a|b)*"  -> Reg.zeroOrMore (Reg.or (Reg.normal ('a'), Reg.normal ('b')))
```
```cpp
"ab*"     -> add (str (normal ('a')), zeroOrMore (normal ('b')))
"(ab)*"   -> zeroOrMore (add (str (normal ('a')), normal ('b')))
"ab|a"    -> orr (add (str (normal ('a')), normal ('b')), normal ('a'))
"a(b|a)"  -> add (str (normal ('a')), orr (normal ('b'), normal ('a')))
"a|b*"    -> orr (normal ('a'), zeroOrMore (normal ('b')))
"(a|b)*"  -> zeroOrMore (orr (normal ('a'), normal ('b')))
```
```python
"ab*"     -> Str([Normal ('a'), ZeroOrMore(Normal('b'))])
"(ab)*"   -> ZeroOrMore(Str([Normal('a'), Normal('b')]))
"ab|a"    -> Or(Str([Normal('a'), Normal('b')]), Normal('a'))
"a(b|a)"  -> Str([Normal('a'), Or(Normal('b'), Normal('a'))])
"a|b*"    -> Or(Normal('a'), ZeroOrMore(Normal('b')))
"(a|b)*"  -> ZeroOrMore(Or(Normal('a'), Normal('b')))
```
```java
"ab*"     -> new Str ([new Normal ('a'), new ZeroOrMore (new Normal ('b'))])
"(ab)*"   -> new ZeroOrMore (new Str ([new Normal ('a'), new Normal ('b')]))
"ab|a"    -> new Or (new Str ([new Normal ('a'), new Normal ('b')]), new Normal ('a'))
"a(b|a)"  -> new Str ([new Normal ('a'), new Or (new Normal ('b'), new Normal ('a'))])
"a|b*"    -> new Or (new Normal ('a'), new ZeroOrMore (new Normal ('b')))
"(a|b)*"  -> new ZeroOrMore (new Or (new Normal ('a'), new Normal ('b')))
```
```kotlin
"ab*"     -> Str ([Normal ('a'), ZeroOrMore (Normal ('b'))])
"(ab)*"   -> ZeroOrMore (Str ([Normal ('a'), Normal ('b')]))
"ab|a"    -> Or (Str ([Normal ('a'), Normal ('b')]), Normal ('a'))
"a(b|a)"  -> Str ([Normal ('a'), Or (Normal ('b'), Normal ('a'))])
"a|b*"    -> Or (Normal ('a'), ZeroOrMore (Normal ('b')))
"(a|b)*"  -> ZeroOrMore (Or (Normal ('a'), Normal ('b')))
```
```javascript
"ab*"     -> new Str([ new Normal('a'), new ZeroOrMore(new Normal ('b')) ])
"(ab)*"   -> new ZeroOrMore(new Str([ new Normal('a'), new Normal('b') ]))
"ab|a"    -> new Or( new Str([ new Normal('a'), new Normal('b') ]), new Normal ('a') )
"a(b|a)"  -> new Str([ new Normal('a'), new Or( new Normal('b'), new Normal('a') ) ])
"a|b*"    -> new Or( new Normal('a'), new ZeroOrMore(new Normal('b')) )
"(a|b)*"  -> new ZeroOrMore(new Or( new Normal('a'), new Normal('b') ))
```

Some examples:

```haskell
"a"          -> Normal 'a'
"ab"         -> Str [ Normal 'a', Normal 'b']
"a.*"        -> Str [ Normal 'a', ZeroOrMore Any ]
"(a.*)|(bb)" -> Or (Str [Normal a, ZeroOrMore Any]) (Str [Normal 'b', Normal 'b'])
```
```c
"a"          -> normal ('a')
"ab"         -> add (str (normal ('a')), normal ('b'))
"a.*"        -> add (str (normal ('a')), zeroOrMore (any ()))
"(a.*)|(bb)" -> or (add (str (normal ('a')), zeroOrMore (any ())), add (str (normal ('b')), normal (b)))
```
```csharp
"a"          -> Reg.normal ('a')
"ab"         -> Reg.add (Reg.str (Reg.normal ('a')), Reg.normal ('b'))
"a.*"        -> Reg.add (Reg.str (Reg.normal ('a')), Reg.zeroOrMore (Reg.any ()))
"(a.*)|(bb)" -> Reg.or (Reg.add (Reg.str (Reg.normal ('a')), Reg.zeroOrMore (Reg.any ())), Reg.add (Reg.str (Reg.normal ('b')), Reg.normal (b)))
```
```cpp
"a"          -> normal ('a')
"ab"         -> add (str (normal ('a')), normal ('b'))
"a.*"        -> add (str (normal ('a')), zeroOrMore (any ()))
"(a.*)|(bb)" -> orr (add (str (normal ('a')), zeroOrMore (any ())), add (str (normal ('b')), normal (b)))
```
```python
"a"          -> Normal('a')
"ab"         -> Str([Normal('a'), Normal('b')])
"a.*"        -> Str([Normal('a'), ZeroOrMore(Any())])
"(a.*)|(bb)" -> Or(Str([Normal('a'), ZeroOrMore(Any())]), Str([Normal('b'), Normal('b')]))
```
```java
"a"          -> new Normal('a')
"ab"         -> new Str([ new Normal('a'), new Normal('b') ])
"a.*"        -> new Str([ new Normal('a'), new ZeroOrMore( new Any() ) ])
"(a.*)|(bb)" -> new Or( new Str([ new Normal('a'), new ZeroOrMore( new Any() ) ]),
                        new Str([ new Normal('b'), new Normal('b') ]) )
```
```kotlin
"a"          -> Normal('a')
"ab"         -> Str([ Normal('a'), Normal('b') ])
"a.*"        -> Str([ Normal('a'), ZeroOrMore( Any() ) ])
"(a.*)|(bb)" -> Or( Str([ Normal('a'), ZeroOrMore( Any() ) ]),
                        Str([ Normal('b'), Normal('b') ]) )
```
```javascript
"a"          -> new Normal('a')
"ab"         -> new Str([ new Normal('a'), new Normal('b') ])
"a.*"        -> new Str([ new Normal('a'), new ZeroOrMore(new Any()) ])
"(a.*)|(bb)" -> new Or( new Str([ new Normal('a'), new ZeroOrMore(new Any()) ])
                      , new Str([ new Normal('b'), new Normal('b') ])
                      )
```

The followings are invalid regexps and the parser should return `Nothing` in Haskell / `0` in C or C++ / `null` in JavaScript or C# / `None` in Python / `new Void()` in Java/`Void()` in Kotlin:

`""`, `")("`, `"*"`, `"a("`, `"()"`, `"a**"`, etc.

Feel free to use any parser combinator libraries available on codewars, or implement the parser "from scratch".