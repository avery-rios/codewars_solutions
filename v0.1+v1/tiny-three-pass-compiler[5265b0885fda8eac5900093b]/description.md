You are writing a three-pass compiler for a simple programming language into a small assembly language.

The programming language has this syntax:

```
    function   ::= '[' arg-list ']' expression

    arg-list   ::= /* nothing */
                 | variable arg-list

    expression ::= term
                 | expression '+' term
                 | expression '-' term

    term       ::= factor
                 | term '*' factor
                 | term '/' factor

    factor     ::= number
                 | variable
                 | '(' expression ')'
```

Variables are strings of alphabetic characters.  Numbers are strings of decimal digits representing integers.  So, for example, a function which computes a<sup>2</sup> + b<sup>2</sup> might look like:

```
    [ a b ] a*a + b*b
```

A function which computes the average of two numbers might look like:

```
    [ first second ] (first + second) / 2
```

You need write a three-pass compiler.  All test cases will be valid programs, so you needn't concentrate on error-handling.

The first pass will be the method `pass1` which takes a string representing a function in the original programming language and will return a (JSON) object that represents that Abstract Syntax Tree.  The Abstract Syntax Tree must use the following representations:

```javascript
    { 'op': '+', 'a': a, 'b': b }    // add subtree a to subtree b
    { 'op': '-', 'a': a, 'b': b }    // subtract subtree b from subtree a
    { 'op': '*', 'a': a, 'b': b }    // multiply subtree a by subtree b
    { 'op': '/', 'a': a, 'b': b }    // divide subtree a from subtree b
    { 'op': 'arg', 'n': n }          // reference to n-th argument, n integer
    { 'op': 'imm', 'n': n }          // immediate value n, n integer
```
```coffeescript
    { 'op': '+', 'a': a, 'b': b }    // add subtree a to subtree b
    { 'op': '-', 'a': a, 'b': b }    // subtract subtree b from subtree a
    { 'op': '*', 'a': a, 'b': b }    // multiply subtree a by subtree b
    { 'op': '/', 'a': a, 'b': b }    // divide subtree a from subtree b
    { 'op': 'arg', 'n': n }          // reference to n-th argument, n integer
    { 'op': 'imm', 'n': n }          // immediate value n, n integer
```
```python
    { 'op': '+', 'a': a, 'b': b }    // add subtree a to subtree b
    { 'op': '-', 'a': a, 'b': b }    // subtract subtree b from subtree a
    { 'op': '*', 'a': a, 'b': b }    // multiply subtree a by subtree b
    { 'op': '/', 'a': a, 'b': b }    // divide subtree a from subtree b
    { 'op': 'arg', 'n': n }          // reference to n-th argument, n integer
    { 'op': 'imm', 'n': n }          // immediate value n, n integer
```
```ruby
    { 'op': '+', 'a': a, 'b': b }    // add subtree a to subtree b
    { 'op': '-', 'a': a, 'b': b }    // subtract subtree b from subtree a
    { 'op': '*', 'a': a, 'b': b }    // multiply subtree a by subtree b
    { 'op': '/', 'a': a, 'b': b }    // divide subtree a from subtree b
    { 'op': 'arg', 'n': n }          // reference to n-th argument, n integer
    { 'op': 'imm', 'n': n }          // immediate value n, n integer
```
```php
    { 'op': '+', 'a': a, 'b': b }    // add subtree a to subtree b
    { 'op': '-', 'a': a, 'b': b }    // subtract subtree b from subtree a
    { 'op': '*', 'a': a, 'b': b }    // multiply subtree a by subtree b
    { 'op': '/', 'a': a, 'b': b }    // divide subtree a from subtree b
    { 'op': 'arg', 'n': n }          // reference to n-th argument, n integer
    { 'op': 'imm', 'n': n }          // immediate value n, n integer
```
```haskell
data AST = Imm Int      -- immediate value
         | Arg Int      -- reference to n-th argument
         | Add AST AST  -- add first to second
         | Sub AST AST  -- subtract second from first
         | Mul AST AST  -- multiply first by second
         | Div AST AST  -- divide first by second
```
```java
  // Each node type implements interface 'Ast' and has the
  // following methods:
  // interface Ast has method 'op()' returning 'String'
  // BinOp has methods 'a()' and 'b()', both return 'Ast'
  // UnOp has method 'n()' returning 'int'
  new BinOp('+', a, b)       // add subtree a to subtree b
  new BinOp('-', a, b)       // subtract subtree b from subtree a
  new BinOp('*', a, b)       // multiply subtree a by subtree b
  new BinOp('/', a, b)       // divide subtree a from subtree b
  new UnOp('arg', n)         // reference to n-th argument, n integer
  new UnOp('imm', n)         // immediate value n, n integer
```
```dart
  // Each node type implements interface 'Ast' and has the
  // following methods:
  // interface Ast has method 'op()' returning 'String'
  // BinOp has methods 'a()' and 'b()', both return 'Ast'
  // UnOp has method 'n()' returning 'int'
  new BinOp('+', a, b)       // add subtree a to subtree b
  new BinOp('-', a, b)       // subtract subtree b from subtree a
  new BinOp('*', a, b)       // multiply subtree a by subtree b
  new BinOp('/', a, b)       // divide subtree a from subtree b
  new UnOp('arg', n)         // reference to n-th argument, n integer
  new UnOp('imm', n)         // immediate value n, n integer
```

```csharp
  // Each node is of type 'Ast' and has the following methods:
  // Ast has method 'op()' returning 'String'
  // BinOp has methods 'a()' and 'b()', both return 'Ast'
  // UnOp has method 'n()' returning 'int'
  new BinOp('+', a, b)       // add subtree a to subtree b
  new BinOp('-', a, b)       // subtract subtree b from subtree a
  new BinOp('*', a, b)       // multiply subtree a by subtree b
  new BinOp('/', a, b)       // divide subtree a from subtree b
  new UnOp('arg', n)         // reference to n-th argument, n integer
  new UnOp('imm', n)         // immediate value n, n integer
```

```cpp
  // Each node is of type 'AST' and has the following fields:
  // 'string op', 'AST* a', 'AST* b', and 'int n'
  AST ("+", a, b)       // add subtree a to subtree b
  AST ("-", a, b)       // subtract subtree b from subtree a
  AST ("*", a, b)       // multiply subtree a by subtree b
  AST ("/", a, b)       // divide subtree a from subtree b
  AST ("arg", n)        // reference to n-th argument, n integer
  AST ("imm", n)        // immediate value n, n integer
```
```ocaml
type ast =
  | Imm of int  (* immediate value *)
  | Arg of int  (* reference to n-th argument *)
  | Add of (ast * ast) (* add first to second *)
  | Sub of (ast * ast) (* subtract second from first *)
  | Mul of (ast * ast) (* multiply first by second *)
  | Div of (ast * ast) (* divide first by second *)
```

```c
  // Each node is a struct of type 'AST' and has the following fields:
  // 'enum op op', 'AST* a', 'AST* b', and 'int n' (unused fields are 0)
  Bin (add, a, b)       // add subtree a to subtree b
  Bin (sub, a, b)       // subtract subtree b from subtree a
  Bin (mul, a, b)       // multiply subtree a by subtree b
  Bin (div, a, b)       // divide subtree a from subtree b
  Arg (n)               // reference to n-th argument, n integer
  Imm (n)               // immediate value n, n integer
```
```rust
    Ast::BinOp("+".to_string(), Box::new(a), Box::new(b) } // add subtree a to subtree b
    Ast::BinOp("-".to_string(), Box::new(a), Box::new(b) } // subtract subtree b from subtree a
    Ast::BinOp("*".to_string(), Box::new(a), Box::new(b) } // multiply subtree a by subtree b
    Ast::BinOp("/".to_string(), Box::new(a), Box::new(b) } // divide subtree a from subtree b
    Ast::UnOp("arg".to_string(), n) // reference to n-th argument, n integer
    Ast::UnOp("imm".to_string(), n) // immediate value n, n integer
```


Note: arguments are indexed from zero.  So, for example, the function

`[ x y ] ( x + y ) / 2` would look like:

```javascript
    { 'op': '/', 'a': { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                                   'b': { 'op': 'arg', 'n': 1 } },
                 'b': { 'op': 'imm', 'n': 2 } }
```
```coffeescript
    { 'op': '/', 'a': { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                                   'b': { 'op': 'arg', 'n': 1 } },
                 'b': { 'op': 'imm', 'n': 2 } }
```
```python
    { 'op': '/', 'a': { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                                   'b': { 'op': 'arg', 'n': 1 } },
                 'b': { 'op': 'imm', 'n': 2 } }
```
```ruby
    { 'op': '/', 'a': { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                                   'b': { 'op': 'arg', 'n': 1 } },
                 'b': { 'op': 'imm', 'n': 2 } }
```
```php
    { 'op': '/', 'a': { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                                   'b': { 'op': 'arg', 'n': 1 } },
                 'b': { 'op': 'imm', 'n': 2 } }
```
```haskell
(Div (Add (Arg 0) (Arg 1))
     (Imm 2))
```
```java
  new BinOp("/", new BinOp("+", new UnOp("arg", 0), new UnOp("arg", 1)), new UnOp("imm", 2))
```
```dart
  new BinOp("/", new BinOp("+", new UnOp("arg", 0), new UnOp("arg", 1)), new UnOp("imm", 2))
```
```csharp
  new BinOp("/", new BinOp("+", new UnOp("arg", 0), new UnOp("arg", 1)), new UnOp("imm", 2))
```
```cpp
  new AST ("/", new AST ("+", new AST ("arg", 0), new AST ("arg", 1)), new AST ("imm", 2))
```
```ocaml
Div(Add(Arg 0,Arg 1), Imm 2)
```
```c
  Bin (div, Bin (add, Arg (0), Arg (1)), Imm (2))
```
```rust
  Ast::BinOp("/".to_string(),
    Box::new(Ast::BinOp("+".to_string(),
        Box::new(Ast::UnOp("arg".to_string(), 0)),
        Box::new(Ast::UnOp("arg".to_string(), 1)))),
    Box::new(Ast::UnOp("imm".to_string(), 2)))
```


The second pass of the compiler will be called `pass2`.  This pass will take the output from `pass1` and return a new Abstract Syntax Tree (with the same format) with all constant expressions reduced as much as possible.  So, if for example, the function is `[ x ] x + 2*5`, the result of `pass1` would be:

```javascript
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': '*', 'a': { 'op': 'imm', 'n': 2 },
                                   'b': { 'op': 'imm', 'n': 5 } } }
```
```coffeescript
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': '*', 'a': { 'op': 'imm', 'n': 2 },
                                   'b': { 'op': 'imm', 'n': 5 } } }
```
```python
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': '*', 'a': { 'op': 'imm', 'n': 2 },
                                   'b': { 'op': 'imm', 'n': 5 } } }
```
```ruby
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': '*', 'a': { 'op': 'imm', 'n': 2 },
                                   'b': { 'op': 'imm', 'n': 5 } } }
```
```php
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': '*', 'a': { 'op': 'imm', 'n': 2 },
                                   'b': { 'op': 'imm', 'n': 5 } } }
```
```haskell
(Add (Arg 0)
     (Mul (Imm 2) (Imm 5)))
```
```java
new BinOp("+", new UnOp("arg", 0), new BinOp("*", new UnOp("imm", 2), new UnOp("imm", 5)))
```
```dart
new BinOp("+", new UnOp("arg", 0), new BinOp("*", new UnOp("imm", 2), new UnOp("imm", 5)))
```
```csharp
new BinOp("+", new UnOp("arg", 0), new BinOp("*", new UnOp("imm", 2), new UnOp("imm", 5)))
```
```cpp
new AST ("+", new AST ("arg", 0), new AST ("*", new AST ("imm", 2), new AST ("imm", 5)))
```
```ocaml
Add(Arg 0, Mul(Imm 2, Imm 5))
```
```c
  Bin (add, Arg (0), Bin (mul, Imm (2), Imm (5)))
```
```rust
Ast::BinOp("+".to_string(),
    Box::new(Ast::UnOp("arg".to_string(), 0)),
    Box::new(Ast::BinOp("*".to_string(),
        Box::new(Ast::UnOp("imm".to_string(), 2)),
        Box::new(Ast::UnOp("imm".to_string(), 5)))))
```

This would be passed into `pass2` which would return:

```javascript
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': 'imm', 'n': 10 } }
```
```coffeescript
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': 'imm', 'n': 10 } }
```
```python
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': 'imm', 'n': 10 } }
```
```ruby
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': 'imm', 'n': 10 } }
```
```php
    { 'op': '+', 'a': { 'op': 'arg', 'n': 0 },
                 'b': { 'op': 'imm', 'n': 10 } }
```
```haskell
(Add (Arg 0) (Imm 10))
```
```java
new BinOp("+", new UnOp("arg", 0), new UnOp("imm", 10))
```
```dart
new BinOp("+", new UnOp("arg", 0), new UnOp("imm", 10))
```
```csharp
new BinOp("+", new UnOp("arg", 0), new UnOp("imm", 10))
```
```cpp
new AST ("+", new AST ("arg", 0), new AST ("imm", 10))
```
```ocaml
Add(Arg 0, Imm 10)
```
```c
  Bin (add, Arg (0), Imm (10))
```
```rust
Ast::BinOp("+".to_string(),
    Box::new(Ast::UnOp("arg".to_string(), 0)),
    Box::new(Box::new(Ast::UnOp("imm".to_string(), 10)))),
```


The third pass of the compiler is `pass3`.  The `pass3` method takes in an Abstract Syntax Tree and returns an array of strings.  Each string is an assembly directive.  You are working on a small processor with two registers (`R0` and `R1`), a stack, and an array of input arguments.  The result of a function is expected to be in `R0`.  The processor supports the following instructions:

```
    "IM n"     // load the constant value n into R0
    "AR n"     // load the n-th input argument into R0
    "SW"       // swap R0 and R1
    "PU"       // push R0 onto the stack
    "PO"       // pop the top value off of the stack into R0
    "AD"       // add R1 to R0 and put the result in R0
    "SU"       // subtract R1 from R0 and put the result in R0
    "MU"       // multiply R0 by R1 and put the result in R0
    "DI"       // divide R0 by R1 and put the result in R0
```

So, one possible return value from `pass3` given the Abstract Syntax Tree shown above from `pass2` is:

```
    [ "IM 10", "SW", "AR 0", "AD" ]
```

Here is a simulator for the target machine.  It takes an array of assembly instructions and an array of arguments and returns the result.
```javascript
function simulate(asm, args) {
	  var r0 = undefined;
	  var r1 = undefined;
	  var stack = [];
	  asm.forEach(function (instruct) {
	    var match = instruct.match(/(IM|AR)\s+(\d+)/) || [ 0, instruct, 0 ];
	    var ins = match[1];
	    var n = match[2] | 0;
	
	    if (ins == 'IM')   { r0 = n; }
	    else if (ins == 'AR') { r0 = args[n]; }
	    else if (ins == 'SW') { var tmp = r0; r0 = r1; r1 = tmp; }
	    else if (ins == 'PU') { stack.push(r0); }
	    else if (ins == 'PO') { r0 = stack.pop(); }
	    else if (ins == 'AD') { r0 += r1; }
	    else if (ins == 'SU') { r0 -= r1; }
	    else if (ins == 'MU') { r0 *= r1; }
	    else if (ins == 'DI') { r0 /= r1; }
	  });
	  return r0;
	}
```
```coffeescript
simulate = (asm, args) ->
  r0 = undefined;
  r1 = undefined;
  stack = [];
  swap = () -> tmp = r0; r0 = r1; r1 = tmp;
  for instruct in asm
    match = instruct.match(/(IM|AR)\s+(\d+)/) || [ 0, instruct, 0 ];
    ins = match[1];
    n = match[2] | 0;

    if (ins == 'IM')      then r0 = n
    else if (ins == 'AR') then r0 = args[n]
    else if (ins == 'SW') then swap()
    else if (ins == 'PU') then stack.push(r0)
    else if (ins == 'PO') then r0 = stack.pop()
    else if (ins == 'AD') then r0 += r1
    else if (ins == 'SU') then r0 -= r1
    else if (ins == 'MU') then r0 *= r1
    else if (ins == 'DI') then r0 /= r1
  r0
```
```python
def simulate(asm, argv):
    r0, r1 = None, None
    stack = []
    for ins in asm:
        if ins[:2] == 'IM' or ins[:2] == 'AR':
            ins, n = ins[:2], int(ins[2:])
        if ins == 'IM':   r0 = n
        elif ins == 'AR': r0 = argv[n]
        elif ins == 'SW': r0, r1 = r1, r0
        elif ins == 'PU': stack.append(r0)
        elif ins == 'PO': r0 = stack.pop()
        elif ins == 'AD': r0 += r1
        elif ins == 'SU': r0 -= r1
        elif ins == 'MU': r0 *= r1
        elif ins == 'DI': r0 /= r1
    return r0
```
```ruby
def simulate(asm, argv)
    r0, r1 = 0, 0
    stack = []
    asm.each do |ins|
        if ins[0..1] == 'IM' or ins[0..1] == 'AR'
            ins, n = ins[0..1], ins[2..-1].to_i
        end
        if ins == 'IM'    then r0 = n
        elsif ins == 'AR' then r0 = argv[n]
        elsif ins == 'SW' then r0, r1 = r1, r0
        elsif ins == 'PU' then stack.push(r0)
        elsif ins == 'PO' then r0 = stack.pop()
        elsif ins == 'AD' then r0 += r1
        elsif ins == 'SU' then r0 -= r1
        elsif ins == 'MU' then r0 *= r1
        elsif ins == 'DI' then r0 /= r1
        end
    end
    return r0
end
```
```php
function simulate($asm, $argv) {
    list($r0, $r1) = [0, 0];
    $stack = [];
    foreach ($asm as $ins) {
        if (substr($ins, 0, 2) == 'IM' || substr($ins, 0, 2) == 'AR') {
            list($ins, $n) = [substr($ins, 0, 2), intval(substr($ins, 2))];
        }
        if ($ins == 'IM')      $r0 = $n;
        else if ($ins == 'AR') $r0 = $argv[$n];
        else if ($ins == 'SW') list($r0, $r1) = [$r1, $r0];
        else if ($ins == 'PU') array_push($stack, $r0);
        else if ($ins == 'PO') $r0 = array_pop($stack);
        else if ($ins == 'AD') $r0 += $r1;
        else if ($ins == 'SU') $r0 -= $r1;
        else if ($ins == 'MU') $r0 *= $r1;
        else if ($ins == 'DI') $r0 /= $r1;
    }
    return $r0;
}
```
```haskell
simulate :: [String] -> [Int] -> Int
simulate asm argv = takeR0 $ foldl' step (0, 0, []) asm where
  step (r0,r1,stack) ins =
    case ins of
      ('I':'M':xs) -> (read xs, r1, stack)
      ('A':'R':xs) -> (argv !! n, r1, stack) where n = read xs
      "SW" -> (r1, r0, stack)
      "PU" -> (r0, r1, r0:stack)
      "PO" -> (head stack, r1, tail stack)
      "AD" -> (r0 + r1, r1, stack)
      "SU" -> (r0 - r1, r1, stack)
      "MU" -> (r0 * r1, r1, stack)
      "DI" -> (r0 `div` r1, r1, stack)
  takeR0 (r0,_,_) = r0
```
```dart

class Simulator {
  static int simulate(List<String> asm, List<int> argv) {
    int r0 = 0;
    int r1 = 0;
    List<int> stack = new List();
    asm.forEach((ins) {
      switch (ins.substring(0, 2)) {
        case "IM":
          r0 = int.parse(ins.substring(2).trim());
          break;
        case "AR":
          r0 = argv[int.parse(ins.substring(2).trim())];
          break;
        case "SW":
          int tmp = r0;
          r0 = r1;
          r1 = tmp;
          break;
        case "PU":
          stack.add(r0);
          break;
        case "PO":
          r0 = stack.removeLast();
          break;
        case "AD":
          r0 += r1;
          break;
        case "SU":
          r0 -= r1;
          break;
        case "MU":
          r0 *= r1;
          break;
        case "DI":
          r0 ~/= r1;
          break;
      }
    });
    return r0;
  }
}
```
```java
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

class Simulator {
  public static int simulate(List<String> asm, int... argv) {
    int r0 = 0;
    int r1 = 0;
    Deque<Integer> stack = new LinkedList<>();
    for (String ins : asm) {
      String code = ins.replaceAll("\\s+[0-9]+", "");
      switch (code) {
        case "IM": r0 = Integer.parseInt(ins.substring(2).trim()); break;
        case "AR": r0 = argv[Integer.parseInt(ins.substring(2).trim())]; break;
        case "SW": int tmp = r0; r0 = r1; r1 = tmp; break;
        case "PU": stack.addLast(r0); break;
        case "PO": r0 = stack.removeLast(); break;
        case "AD": r0 += r1; break;
        case "SU": r0 -= r1; break;
        case "MU": r0 *= r1; break;
        case "DI": r0 /= r1; break;
      }
    }
    return r0;
  }
}
```
```csharp
using System;
using System.Collections.Generic;

public class Simulator
{
  public static int simulate(List<string> asm, int[] argv)
  {
    int r0 = 0;
    int r1 = 0;
    List<int> stack = new List<int>();
    foreach (string ins in asm)
    {
      string code = ins.Substring(0,2);
      switch (code)
      {
        case "IM": r0 = Int32.Parse(ins.Substring(2).Trim()); break;
        case "AR": r0 = argv[Int32.Parse(ins.Substring(2).Trim())]; break;
        case "SW": int tmp = r0; r0 = r1; r1 = tmp; break;
        case "PU": stack.Add(r0); break;
        case "PO": r0 = stack[stack.Count - 1]; stack.RemoveAt(stack.Count - 1); break;
        case "AD": r0 += r1; break;
        case "SU": r0 -= r1; break;
        case "MU": r0 *= r1; break;
        case "DI": r0 /= r1; break;
      }
    }
    return r0;
  }
}
```
```cpp
#include <vector>
#include <stack>
#include <string>
#include <utility>

using namespace std;

int simulate (const vector <string> &assembly, const vector <int> &argv) {
  int r0 = 0, r1 = 0;
  stack <int> istack;
  for (auto &ins : assembly) {
    string code = ins.substr (0, 2);
         if (code == "IM") { r0 = stoi (ins.substr (3)); }
    else if (code == "AR") { r0 = argv.at (stoi (ins.substr (3))); }
    else if (code == "SW") { swap (r0, r1); }
    else if (code == "PU") { istack.push (r0); }
    else if (code == "PO") { r0 = istack.top (); istack.pop (); }
    else if (code == "AD") { r0 += r1; }
    else if (code == "SU") { r0 -= r1; }
    else if (code == "MU") { r0 *= r1; }
    else if (code == "DI") { r0 /= r1; }
  }
  return r0;
}
```
```ocaml
let rec simualte : string list * int list -> int =
  let stack = Stack.create () in
  let r0 = ref 0 in
  let r1 = ref 0 in
  function
  | ([],argumets) -> !r0
  | ("SU"::lst,argumets) ->
     r0 := !r0 - !r1;
     simualte(lst,argumets)
  | ("DI"::lst,argumets) ->
     r0 := !r0 / !r1;
     simualte(lst,argumets)
  | ("MU"::lst,argumets) ->
     r0 := !r0 * !r1;
     simualte(lst,argumets)
  | ("AD"::lst,argumets) ->
     r0 := !r0 + !r1;
     simualte(lst,argumets)
  | ("PU"::lst,argumets) ->
     Stack.push !r0 stack;
     simualte(lst,argumets)
  | ("PO"::lst,argumets) ->
     r0 := (Stack.pop stack);
     simualte(lst,argumets)
  | ("SW"::lst,argumets) ->
     let tmp = !r0 in
     r0 := !r1;
     r1 := tmp;
     simualte(lst,argumets)
  | (op::lst,argumets) ->
     let op_code = String.sub op 0 2 in
     let value =
       int_of_string
         (String.sub op 3 ((String.length op) - 3))
     in
     match op_code with
     | "IM" ->
        r0 := value;
        simualte(lst,argumets)
     | "AR" ->
        r0 := List.nth argumets value;
        simualte(lst,argumets)
     | _ -> raise (CompilerError "bad assembly")

```

```c
#include <stdlib.h>
#include <string.h>

// stack push (int) and pop () function defintions

int simulate (const char *ins, const int *args) {
  int r0 = 0, r1 = 0, t;
  for (; ins && *ins; (ins = strchr (ins, '\n')) ? ++ins : 0x60d1510f)
         if (!memcmp (ins, "IM", 2)) r0 = atoi (ins+3);
    else if (!memcmp (ins, "AR", 2)) r0 = args[atoi (ins+3)];
    else if (!memcmp (ins, "SW", 2)) t = r0, r0 = r1, r1 = t;
    else if (!memcmp (ins, "PU", 2)) push (r0);
    else if (!memcmp (ins, "PO", 2)) r0 = pop ();
    else if (!memcmp (ins, "AD", 2)) r0 += r1;
    else if (!memcmp (ins, "SU", 2)) r0 -= r1;
    else if (!memcmp (ins, "MU", 2)) r0 *= r1;
    else if (!memcmp (ins, "DI", 2)) r0 /= r1;
  return r0;
}
```
```rust
fn simulate(assembly : Vec<&str>, argv : Vec<i32>) -> i32 {
  let mut r = (0, 0);
  let mut stack : Vec<i32> = vec![];
  
  for ins in assembly {
    let mut ws = ins.split_whitespace();
    match ws.next() {
      Some("IM") => r.0 = i32::from_str_radix(ws.next().unwrap(), 10).unwrap(),
      Some("AR") => r.0 = argv[i32::from_str_radix(ws.next().unwrap(), 10).unwrap() as usize],
      Some("SW") => r = (r.1,r.0),
      Some("PU") => stack.push(r.0),
      Some("PO") => r.0 = stack.pop().unwrap(),
      Some("AD") => r.0 += r.1,
      Some("SU") => r.0 -= r.1,
      Some("MU") => r.0 *= r.1,
      Some("DI") => r.0 /= r.1,
      _ => panic!("Invalid instruction encountered"),
    }
  }
  r.0
}
```
