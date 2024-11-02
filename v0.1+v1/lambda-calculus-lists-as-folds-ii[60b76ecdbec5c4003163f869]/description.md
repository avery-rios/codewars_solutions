In Lambda Calculus, lists can be represented as their right fold. A right fold <sup>[wiki](https://en.wikipedia.org/wiki/Fold_(higher-order_function))</sup> takes a combining function and an initial value, and returns a single combined value for the whole list, eg.:  

```
< x y z > = λ c n. c x (c y (c z n))
```

~~~if:javascript,
in JavaScript syntax:  

```javascript
[ x, y, z ] = c => n => c(x)(c(y)(c(z)(n))) ;
```
~~~
~~~if:haskell,
in Haskell syntax:  

```haskell
infixr _ `c`
[ x, y, z ] = \ c n -> x `c` y `c` z `c` n
```
~~~

A list is not just the data in it; it also encapsulates operations on it. This representation encodes both a list's data and all possible operations on it, because, with the right combining function and initial value, _any_ operation on a list can be expressed as a right fold, including left folds and folds over multiple lists at once.  

Other datatypes can also be represented. This kata uses Peano encoding ( with an upper bound ) for numbers and Church encoding for booleans, option types and tuples.  
All these representations can be given type in System F <sup>[wiki](https://en.wikipedia.org/wiki/System_F)</sup>, and therefore in Haskell.  
Note that lists can also contain unencoded native Haskell datatypes like `Char`s. Lists are agnostic to the type of their element, which is simply a type parameter.  

Because the focus of this kata is on lists, type definitions, instance constructors and deconstructors, and some helper operations, will be provided for other types. For lists, you will only get the type definition, the primitive constructor and the instance deconstructor.  

For technical reasons really, `foldr` takes its arguments in the order: list, combining function, initial value. `option`, `uncurry` also take their arguments in non-standard order.  
For consistency, `foldl`, `scanl` and `scanr` take their arguments in this same order.  

<details>
<summary><code>Preloaded</code> ( click to expand )</summary>

#### `List a` ( cf. `[]` )

primitive constructor: `List :: ((a -> z -> z) -> z -> z) -> List a`  
instance deconstructor: `foldr :: List a -> (a -> z -> z) -> z -> z`  
<sup>*</sup> this leads to `foldr xs fn z` being the equivalent of `foldr fn z xs` ( note <span style="color:magenta">order of arguments</span> )  

#### `Number` ( cf. `Natural` )

`Number`s are unsigned and _bounded_ ( to 2<sup>64</sup> - 1, which is enough for this kata )  
instance constructors: use regular numbers  
instance deconstructors: N/A  
helpers:  
`zero :: Number -> Boolean` to compare a number to `0`  
`succ, pred :: Number -> Number` to increase or decrease a number  
`plus, times :: Number -> Number -> Number` to add or multiply two numbers  
_not_ provided: instance methods from `Eq` and `Ord`  

#### <a name="Boolean"></a>`Boolean` ( cf. `Bool` )

instance constructors: `true, false :: Boolean`  
instance deconstructor: `(?) :: Boolean -> z -> z -> z`  
<sup>*</sup> this leads to `x ? t $ f` being the equivalent of `if x then t else f`  
helpers:  
`or, and :: Boolean -> Boolean -> Boolean` to disjunct or conjunct two booleans  
`not :: Boolean -> Boolean` to negate a boolean  

#### `Option a` ( cf. `Maybe` )

instance constructors: `nothing :: Option a`, `just :: a -> Option a`  
instance deconstructor: `option :: Option a -> z -> (a -> z) -> z`  
<sup>*</sup> this leads to `option x n j` being the equivalent of `maybe n j x` ( note <span style="color:magenta">order of arguments</span> )  
helper: `fmap :: (a -> x) -> Option a -> Option x` to map over an optional value ( this function is polymorphic over the type within `Option`, but <span style="color:magenta">not</span> polymorphic over the `Option` type itself )  
_not_ provided: `isNothing`, `isJust`  

#### `Pair a b` ( cf. `(,)` )

`Pair`s are a 2-tuple  
instance constructor: `pair :: a -> b -> Pair a b`  
instance deconstructor: `uncurry :: Pair a b -> (a -> b -> z) -> z`  
<sup>*</sup> this leads to `uncurry xy fn` being the equivalent of `uncurry fn (x,y)` ( note <span style="color:magenta">order of arguments</span> )  
helpers:  
`fst :: Pair a b -> a` to extract the left value of a pair  
`snd :: Pair a b -> b` to extract the right value of a pair  
`first :: (a -> z) -> Pair a b -> Pair z b` to map over the left value of a pair  
`second :: (b -> z) -> Pair a b -> Pair a z` to map over the right value of a pair  
`both :: (a -> x) -> Pair a a -> Pair x x` to map over both values of a pair  
`double :: (a -> x) -> (b -> y) -> Pair a b -> Pair x y` to map over both values of a pair  
_not_ provided: `swap`  

#### `Prelude` reexports

`$`, `undefined` are reexported for convenience.  
_not_ provided: `B`, `C`, `K`, `I`, `S`, `W`, `Y`, or any other combinators;  
you can do without `(.)`, `flip`, `const`, `id`, `ap`, `join`, `fix`, define your own, or import them ( `(.)` will not be usable )  
</details>

## Task

Define the following operations on / with / to / from Lambda Calculus lists implemented as right folds.  

You can define constants in Lambda Calculus syntax only: variables, abstractions and applications. You can define and use helper constants. Recursion is not restricted. See also [Syntax](#Syntax) below.  

instance constructors:  

```haskell
cons :: a -> List a -> List a  --  to prepend an element to a list
nil :: List a                  --  the empty list
```

helpers: these are used extensively for testing

```haskell
sum, product :: List Number -> Number  --  add or multiply together all numbers in a list
```

also, `take` is used for testing infinite lists. you will get recognisable failure messages if any of these is missing.

more instance constructors:  

```haskell
iterate :: (a -> a) -> a -> List a  --  to build an infinite list by repeated transformation of a seed
repeat :: a -> List a               --  to build an infinite list by repeating a seed
cycle :: List a -> List a           --  to build an infinite list by repeating elements of a seed
                                    --  remember: nil -> undefined
replicate :: Number -> a -> List a  --  to build a finite list by repeating seed values
```

more helpers:  

```haskell
null      :: List a -> Boolean
length    :: List a -> Number
snoc      :: List a -> a      -> List a
append    :: List a -> List a -> List a
concat    :: List (List a)    -> List a

map       :: (a -> z)       -> List a -> List z
filter    :: (a -> Boolean) -> List a -> List a

take      :: Number      -> List a -> List a
drop      :: Number      -> List a -> List a
splitAt   :: Number      -> List a -> Pair (List a) (List a)
get       :: Number      -> List a -> Option a
set       :: Number -> a -> List a -> List a

any       :: (a -> Boolean)      -> List a -> Boolean
all       :: (a -> Boolean)      -> List a -> Boolean
find      :: (a -> Boolean)      -> List a -> Option a
findIndex :: (a -> Boolean)      -> List a -> Option Number
partition :: (a -> Boolean)      -> List a -> Pair (List a) (List a)
span      :: (a -> Boolean)      -> List a -> Pair (List a) (List a)
minimumBy :: (a -> a -> Boolean) -> List a -> Option a  --
maximumBy :: (a -> a -> Boolean) -> List a -> Option a  --  interpret comparator as LEQ (<=)
sortBy    :: (a -> a -> Boolean) -> List a -> List a    --

foldl     :: List a -> (z -> a -> z) -> z -> z       --
scanl     :: List a -> (z -> a -> z) -> z -> List z  --  note order of arguments
scanr     :: List a -> (a -> z -> z) -> z -> List z  --

reverse   :: List a -> List a
head      :: List a -> Option a
tail      :: List a -> Option (List a)
init      :: List a -> Option (List a)
last      :: List a -> Option a

zip       ::                  List a -> List b -> List (Pair a b)
unzip     ::                  List (Pair a b)  -> Pair (List a) (List b)
zipWith   :: (a -> b -> z) -> List a -> List b -> List z
```

_not_ expected: `elem`, `elemIndex`. There is no polymorphic notion of equality in Lambda Calculus. Use `find`, `findIndex`.  

#### <a name="Syntax"></a>Syntax

* You can have a `module` line.  
* You can `import Prelude` and `Preloaded`, unqualified and unaliased.  
  You need _exceedingly few_ imports from `Prelude`. By possibly defining a few combinators yourself, you probably need _none._  
* You can define `newtype`s.  
* You can define type signatures.  
* You can define values and functions.  
* You can have comments, with `--`, not with `{- -}`. Thus, you cannot have pragmas.  
* You can have empty lines.  
* You can have whitespace.  
* Every line has to be valid on its own. The syntax checker does not recognise line continuations.  

Relaxations from lambda calculus syntax:  

* Named function definition syntax can be used as well as anonymous ( lambda ) syntax.  
* `where` clauses can be used. Break a line of code _either_ before _or_ after `where`.  
   Without `where`, lines might become infeasably long.  
* Haskell `_` can be used to skip a binding.  
* Haskell `$` can be used instead of endless parentheses.  
* `?` can be used ( see [`Boolean`](#Boolean) ).  

`?` and `$` are the _only_ allowed operators. Specifically, there is  

* no `(==)`. Lambda Calculus doesn't have this. You can build your own for specific datatypes.  
* no `(.)`. Build your own composition combinator.  
* no qualified names.  
* no infix notation.  
* no pattern matching.  
* no guards.  
* no `let .. in ..`. Lambda Calculus does this functionally. Use `where`, or an applied lambda.  

#### Laziness

Laziness allows for infinite lists and efficiency with finite lists. If an operation is defined over a list prefix, the suffix can be `undefined`. In appropriate cases, this will be tested, both in `Example` and `Submit` testing.  
<sup>*</sup> The list spine has to be defined one element further than the elements need to be ( because that is where its `foldr` will be coming from ). It will be.  

#### Performance

Simulating pattern matching on lists might lead to unsatisfactory performance. Aim to implement your solutions with a single `foldr` per list argument. In appropriate cases, this will be tested, in `Submit` testing only.  