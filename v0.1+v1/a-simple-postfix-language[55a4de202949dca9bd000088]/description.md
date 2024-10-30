```if:haskell
The goal of this kata is to embed a stack based language into Haskell. Languages such as forth have a number of simple commands such as `push` but are written in a postfix style. Haskell only has support for prefix and infix function application, can we directly embed such langauges into Haskell?
```
```if:ocaml
The goal of this kata is to embed a stack based language into OCaml. Languages such as forth have a number of simple commands such as `push` but are written in a postfix style. OCaml only has support for prefix and infix function application, can we directly embed such langauges into OCaml?
```
```if:fsharp
The goal of this kata is to embed a stack based language into F#. Languages such as forth have a number of simple commands such as `push` but are written in a postfix style. F# only has support for prefix and infix function application, can we directly embed such langauges into F#?
```

We will only use 4 instructions.
```if:haskell
1. `begin`   - Marks the start of a program.
2. `end`     - Marks the end of a program and returns the top element of the stack.
```
```if:ocaml
1. `begin_`   - Marks the start of a program. (`begin` is reserved in OCaml)
2. `end_`     - Marks the end of a program and returns the top element of the stack. (`end` is reserved in OCaml)
```
```if:fsharp
1. `begin_`   - Marks the start of a program. (`begin` is reserved in F#)
2. `end_`     - Marks the end of a program and returns the top element of the stack. (`end` is reserved in F#)
```
3. `push n`  - Pushes an integer onto he stack.
4. `add`     - Adds together the top two elements on the stack.

Here are some examples of programs written using these commands.

```haskell
f = begin push 2 push 3 add end
  = 5
  
g = begin push 1 push 1 add push 2 add end
  = 4
```
```ocaml
f = begin_ push 2 push 3 add end_
  = 5
  
g = begin_ push 1 push 1 add push 2 add end_
  = 4
```
```fsharp
f = begin_ push 2 push 3 add end_
  = 5
  
g = begin_ push 1 push 1 add push 2 add end_
  = 4
```

There are several possible implementations. The two suggestions below are not required in order to complete this kata but further challenges if you so desire.  

1. An invalid program should raise a type error rather than a runtime error.
2. Your implementation should allow programs such as.. 
    ```haskell
    bad = begin push 1 push 1 push 1 push 1 push 1 push 1 push 1 push 1 push 1
            add add add add add add add add end
    ```
    ```ocaml
    bad = begin_ push 1 push 1 push 1 push 1 push 1 push 1 push 1 push 1 push 1
            add add add add add add add add end_
    ```
    ```fsharp
    bad = begin_ push 1 push 1 push 1 push 1 push 1 push 1 push 1 push 1 push 1
            add add add add add add add add end_
    ```
```haskell
    The inferred type of a basic implementation is exponential in size to the expression. This causes type inference to take too long.
    Hint: Use a typeclass
    Hint: http://chrisdone.com/posts/haskell-constraint-trick
```
    
     

