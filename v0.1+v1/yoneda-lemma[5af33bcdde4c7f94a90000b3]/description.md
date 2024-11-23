In this kata you will prove [Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma).
<br>
Let's
```haskell
type Hom a = (->) a -- = (a ->)
type Nat f g = forall x. f x -> g x
```
Accordingly to Yoneda lemma, the `Nat (Hom a) f` [natural transformation](https://en.wikipedia.org/wiki/Natural_transformation) and `f a` (where `f` is a covariant functor) are isomorphic, so your task is to implement 2 functions:
```haskell
to :: Functor f => Nat (Hom a) f -> f a
from :: Functof f => f a -> Nat (Hom a) f
```
and 2 functions for [contravariant](https://en.wikipedia.org/wiki/Functor#Covariance_and_contravariance) version:
```haskell
type CoHom a = Op a -- wrapped (-> a), see code

to' :: Contravariant f => Nat (CoHom a) f -> f a
from' :: Contravariant f => f a -> Nat (CoHom a) f
```
Then you will count some natural transformations (see code).
<br>
<br>
<br>

P. S. Good tutorial about Yoneda Lemma: [Understanding Yoneda](https://bartoszmilewski.com/2013/05/15/understanding-yoneda/).
<br>

P. P. S. For categorically inclined people:
<br>
<img src="https://upload.wikimedia.org/wikipedia/commons/b/b1/Yoneda_lemma_cd.svg" alt="prove">
<br>
<br>

In category theory, category of functors from <i>A</i> to <i>B</i> is usually denoted as <i><b>B<sup>A</sup></b></i>.
<br>
Supposing, that <i>A</i> has 3 objects and <i>B</i> has 2, how many functors there are in <i>B<sup>A</sup></i>?