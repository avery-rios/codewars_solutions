The goal of this kata is to write a module that automates the parsing of operators (the bottom of this page contains important information, don't forget to read it :D).

The module should export the function ```parseOperators```, which we can use, for example, like this:

```
expressionP = parseOperators [L [plusP, subtractP], L [multP, divP], R [exponentialP]] numberP
```

```expressionP``` will then be a parser for arithmetical expressions using the following operators:

 * "+" and "-" (left-associative (L), and lowest precedence);
 * "\*" and "/" (also left-associative (L), and higher in precedence);
 * "^" (right-associative (R), and highest in precedence). 

Let's look at the ```parseOperators``` function in more detail:

```
-- | Accept two arguments: 
-- | (1) A list of type [Associativity [ReadP a]], which contains parsers for
-- | operators (ReadP a). Each item of type Associativity [ReadP a] contains
-- | a group of operator parsers of the same precedence and associativity; 
-- | these groups are listed in order of precedence (lowest to highest).
-- | (2) A parser for the terms.
-- | And return a parser for operator expressions that yields a parse tree. 
parseOperators :: [Associativity [ReadP a]] -> ReadP b -> ReadP (OpTree a b)
```

```parseOperators``` references the following types:

```ReadP``` -- a type for parsers exported by ```Text.ParserCombinators.ReadP```.

```
-- | Type for specifying the assocativity of operators: left, right, or none.
data Associativity a = L a | R a | NoAssociativity a
                     deriving (Show, Eq, Functor)

-- | Type for operator parse results. 'a' is the type of the operator, 'b'
-- | of the terms.
data OpTree a b = Op (OpTree a b) a (OpTree a b) 
                | Term b 
                deriving (Show, Eq, Functor)
```

As well as ```parseOperators```, ```Associativity(..)```, and ```OpTree(..)```, the module should also export the following auxiliary functions:

```
-- | Transform an OpTree using the given function.
foldTree :: (a -> b -> b -> b) -> OpTree a b -> b

-- | Return a parser such that: given 'op s a', if s matches, the parser 
-- | returns a.
op :: String -> a -> ReadP a
```

Here's an example of how it works:

```
arithOps :: [Associativity [ReadP String]]
arithOps = 
    map (fmap (map (\s -> op s s) . words)) 
        [ R "&& ||", NoAssociativity "< > =", L "+ -", L "* /", R "^"]

arithParser :: ReadP (OpTree String String) 
arithParser = parseOperators arithOps (munch1 isDigit) <* eof

brackets :: OpTree String String -> String
brackets = foldTree (\o x y -> '(' : x ++ o ++ y ++ ")")

λ > readP_to_S arithParser "5 - 2 - 1 > 3"
[(Op (Op (Op (Term "5") "-" (Term "2")) "-" (Term "1")) ">" (Term "3"),"")]

λ > brackets (Op (Op (Op (Term "5") "-" (Term "2")) "-" (Term "1")) ">" (Term "3"))
"(((5-2)-1)>3)"
```

# Notes:

1. ```parseOperators``` should ignore whitespace between terms and operators, but it should not consume trailing whitespace, and it should fail if the expression is preceded by whitespace. Likewise, ```op``` should not consume preceding or trailing whitespace. 
2. ```parseOperators``` should recognise parentheses (..) and parse them appropriately. 
3. It is the responsibility of the term parser given as an argument to ```parseOperators``` to avoid consuming the operators. In other words, ```readP_to_S (parseOperators arithOps (munch (const True))) "1 + 3 / 5"``` should return ```Term "1 + 3 / 5"```.  
