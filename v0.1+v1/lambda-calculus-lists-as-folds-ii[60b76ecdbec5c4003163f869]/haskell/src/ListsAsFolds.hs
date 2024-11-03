module ListsAsFolds (cons, nil, sum, product, iterate, repeat, cycle, replicate, null, length, snoc, append, concat, map, filter, take, drop, splitAt, get, set, any, all, find, findIndex, partition, span, minimumBy, maximumBy, sortBy, foldl, scanl, scanr, reverse, head, tail, init, last, zip, unzip, zipWith) where

import Preloaded
import Prelude ()

const :: p1 -> p2 -> p1
const v _ = v

id :: p -> p
id v = v

-- primitive operations

cons :: a -> List a -> List a
cons h t = List (\f i -> f h (foldr t f i))

nil :: List a
nil = List (\_ i -> i)

singleton :: a -> List a
singleton v = List (\f i -> f v i)

-- derived operations

sum, product :: List Number -> Number
sum l = foldr l plus 0
product l = foldr l times 1

-- derived constructors

iterate :: (a -> a) -> a -> List a
iterate fi iv = List (\f i -> f iv (foldr (iterate fi (fi iv)) f i))

repeat :: a -> List a
repeat a = List (\f i -> f a (foldr (repeat a) f i))

cycle :: List a -> List a
cycle l = null l ? undefined $ List (\f i -> foldr l f (foldr (cycle l) f i))

replicate :: Number -> a -> List a
replicate n v = List (\f i -> zero n ? i $ f v (foldr (replicate (pred n) v) f i))

-- more derived operations

null :: List a -> Boolean
null l = foldr l (\_ _ -> false) true

length :: List a -> Number
length l = foldr l (\_ n -> succ n) 0

snoc :: List a -> a -> List a
snoc l v = List (\f i -> foldr l f (f v i))

append :: List a -> List a -> List a
append l1 l2 = List (\f i -> foldr l1 f (foldr l2 f i))

concat :: List (List a) -> List a
concat l = List (\f i -> foldr l (\v -> foldr v f) i)

map :: (a -> z) -> List a -> List z
map mf l = List (\f i -> foldr l (\v -> f (mf v)) i)

filter :: (a -> Boolean) -> List a -> List a
filter ff l = List (\f i -> foldr l (\v a -> (?) (ff v) (f v a) a) i)

take :: Number -> List a -> List a
take n l = List (\f i -> foldr l (\v nf idx -> zero idx ? i $ f v (nf (pred idx))) (const i) n)

drop :: Number -> List a -> List a
drop n l = List (\f i -> foldr l (\v nf idx -> zero idx ? f v (nf 0) $ nf (pred idx)) (const i) n)

splitAt :: Number -> List a -> Pair (List a) (List a)
splitAt n l = foldr l iter (\_ -> pair nil nil) n
  where iter v nf idx = zero idx ? left $ right
          where left = pair nil (cons v (snd (nf 0)))
                right = first (cons v) (nf (pred idx))

get :: Number -> List a -> Option a
get n l = foldr l iter (const nothing) n
  where iter v nf idx = (?) (zero idx) (just v) (nf (pred idx))

set :: Number -> a -> List a -> List a
set n sv l = List (\f i -> foldr l (iter f) (\_ _ -> i) n true)
  where iter f v nf idx needSet = and (zero idx) needSet ? updated $ notUpdated
          where updated = f sv (nf 0 false)
                notUpdated = f v (nf (pred idx) needSet)

any :: (a -> Boolean) -> List a -> Boolean
any f l = foldr (map f l) or false

all :: (a -> Boolean) -> List a -> Boolean
all f l = foldr (map f l) and true

find :: (a -> Boolean) -> List a -> Option a
find f l = foldr l (\v a -> (?) (f v) (just v) a) nothing

findIndex :: (a -> Boolean) -> List a -> Option Number
findIndex f l = foldr l iter (const nothing) 0
  where iter v nf idx = f v ? just idx $ nf (succ idx)

partition :: (a -> Boolean) -> List a -> Pair (List a) (List a)
partition pf l = foldr l iter (pair nil nil)
  where iter v p = pf v ? first (cons v) p $ second (cons v) p

span :: (a -> Boolean) -> List a -> Pair (List a) (List a)
span f l = foldr l iter (\_ -> pair nil nil) true
  where iter v nf begin = and begin (f v) ? left $ right
          where left = first (cons v) (nf true)
                right = pair nil (cons v (snd (nf false)))

minimumBy :: (a -> a -> Boolean) -> List a -> Option a
minimumBy mf l = foldr l iter nothing
  where iter v a = option a (just v) (update v)
        update v v1 = (?) (mf v v1) (just v) (just v1)

maximumBy :: (a -> a -> Boolean) -> List a -> Option a
maximumBy mf = minimumBy (\l r -> not (mf l r))

splitMaxBy :: (a -> a -> Boolean) -> List a -> Pair (Option a) (List a)
splitMaxBy mf l = foldr l iter (pair nothing nil)
  where iter v pv = option (fst pv) (pair (just v) (snd pv)) (update v pv)
        update v pv v1 = mf v v1 ? vLeV1 $ v1LeV
          where vLeV1 = pair (just v1) (cons v (snd pv))
                v1LeV = pair (just v) (cons v1 (snd pv))

sortBy :: (a -> a -> Boolean) -> List a -> List a
sortBy mf = iter nil
  where iter acc l = option (fst mxP) acc (\v -> iter (cons v acc) (snd mxP))
          where mxP = splitMaxBy mf l

foldl :: List a -> (z -> a -> z) -> z -> z
foldl l lf = foldr l (\v vf inner -> vf (lf inner v)) id

scanl :: List a -> (z -> a -> z) -> z -> List z
scanl l sf si = snd (foldl l iter (pair si (singleton si)))
  where iter pv v = pair (sf (fst pv) v) (snoc (snd pv) (sf (fst pv) v))

scanr :: List a -> (a -> z -> z) -> z -> List z
scanr l sf si = snd (foldr l iter (pair si (singleton si)))
  where iter v pv = pair newV (cons newV (snd pv))
          where newV = sf v (fst pv)

reverse :: List a -> List a
reverse l = foldl l (\acc v -> cons v acc) nil

head :: List a -> Option a
head l = foldr l (\v _ -> just v) nothing

tail :: List a -> Option (List a)
tail l = snd (foldr l iter (pair nil nothing))
  where iter v p = pair (cons v (fst p)) (just (fst p))

init :: List a -> Option (List a)
init l = fst (foldl l iter (pair nothing nil))
  where iter p v = pair (just (snd p)) (snoc (snd p) v)

last :: List a -> Option a
last l = foldr l (\v o -> option o (just v) just) nothing

zip :: List a -> List b -> List (Pair a b)
zip = zipWith pair

unzip :: List (Pair a b) -> Pair (List a) (List b)
unzip l = foldr l (\v -> double (cons (fst v)) (cons (snd v))) (pair nil nil)

newtype Next a = Next {getNext :: Option (Pair a (Next a))}

zipWith :: (a -> b -> z) -> List a -> List b -> List z
zipWith f l0 l1 = foldr l1 iter (const nil) nextL0
  where iter v1 nf nxt = option (getNext nxt) nil zipH
          where zipH v0 = cons (f (fst v0) v1) (nf (snd v0))
        nextL0 = foldr l0 (\v nx -> Next (just (pair v nx))) (Next nothing)
