Write a typed interpreter for the finally tagless style language given. The language will use de Bruijn style names and includes a fixed point and functions for manipulating integers and booleans.

An example expression would be

    \a -> \b -> a + b
    
which, rendered as a `Term` is

    ex :: Term (Int -> Int -> Int)
    ex = lambda (lambda (add (before here) here))
    
The use of de Bruijn indices means that instead of denoting variables by name they are denote by position instead. So, `here` is the variable most recently bound, and `before here` is the variable bound just prior to `here`.

**Hint:** This technique is discussed in [a lecture from Oleg Kiselyov](http://okmij.org/ftp/tagless-final/course/lecture.pdf).