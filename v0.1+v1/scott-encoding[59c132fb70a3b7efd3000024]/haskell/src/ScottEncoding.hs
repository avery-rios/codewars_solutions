{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ScottEncoding where

import Prelude hiding (concat, curry, foldl, foldr, fst, length, map, null, snd, take, uncurry, zip, (++))

newtype SMaybe a = SMaybe {runMaybe :: forall b. b -> (a -> b) -> b}

newtype SList a = SList {runList :: forall b. b -> (a -> SList a -> b) -> b}

nilSL :: SList a
nilSL = SList (\i _ -> i)

newtype SEither a b = SEither {runEither :: forall c. (a -> c) -> (b -> c) -> c}

newtype SPair a b = SPair {runPair :: forall c. (a -> b -> c) -> c}

toPair :: SPair a b -> (a, b)
toPair sp = runPair sp (,)

fromPair :: (a, b) -> SPair a b
fromPair (a, b) = SPair (\f -> f a b)

fst :: SPair a b -> a
fst (SPair sp) = sp (\a _ -> a)

snd :: SPair a b -> b
snd (SPair sp) = sp (\_ b -> b)

swap :: SPair a b -> SPair b a
swap (SPair sp) = SPair (\f -> sp (\a b -> f b a))

curry :: (SPair a b -> c) -> (a -> b -> c)
curry f a b = f (SPair (\g -> g a b))

uncurry :: (a -> b -> c) -> (SPair a b -> c)
uncurry f (SPair sp) = sp f

toMaybe :: SMaybe a -> Maybe a
toMaybe (SMaybe sm) = sm Nothing Just

fromMaybe :: Maybe a -> SMaybe a
fromMaybe (Just a) = SMaybe (\_ f -> f a)
fromMaybe Nothing = SMaybe (\a _ -> a)

isJust :: SMaybe a -> Bool
isJust (SMaybe sm) = sm False (const True)

isNothing :: SMaybe a -> Bool
isNothing (SMaybe sm) = sm True (const False)

catMaybes :: SList (SMaybe a) -> SList a
catMaybes (SList sl) =
  SList
    ( \i fc ->
        sl
          i
          ( \(SMaybe sm) t ->
              sm
                (runList (catMaybes t) i fc)
                (\v -> fc v (catMaybes t))
          )
    )

toEither :: SEither a b -> Either a b
toEither (SEither se) = se Left Right

fromEither :: Either a b -> SEither a b
fromEither (Left l) = SEither (\fl _ -> fl l)
fromEither (Right r) = SEither (\_ fr -> fr r)

isLeft :: SEither a b -> Bool
isLeft (SEither se) = se (const True) (const False)

isRight :: SEither a b -> Bool
isRight (SEither se) = se (const False) (const True)

partition :: SList (SEither a b) -> SPair (SList a) (SList b)
partition (SList sl) =
  sl
    (fromPair (nilSL, nilSL))
    ( \(SEither se) t ->
        let SPair pt = partition t
         in se
              (\l -> pt (\ls rs -> fromPair (cons l ls, rs)))
              (\r -> pt (\ls rs -> fromPair (ls, cons r rs)))
    )

toList :: SList a -> [a]
toList (SList sl) = sl [] (\h t -> h : toList t)

fromList :: [a] -> SList a
fromList [] = nilSL
fromList (h : t) = SList (\_ fc -> fc h (fromList t))

cons :: a -> SList a -> SList a
cons a sl = SList (\_ fc -> fc a sl)

concat :: SList a -> SList a -> SList a
concat (SList sla) lb@(SList slb) =
  SList (\i fc -> sla (slb i fc) (\h t -> fc h (concat t lb)))

null :: SList a -> Bool
null (SList sl) = sl True (\_ _ -> False)

length :: SList a -> Int
length (SList sl) = sl 0 (\_ t -> 1 + length t)

map :: (a -> b) -> SList a -> SList b
map f (SList sl) = SList (\i fc -> sl i (\h t -> fc (f h) (map f t)))

zip :: SList a -> SList b -> SList (SPair a b)
zip (SList sla) (SList slb) =
  SList
    ( \i fc ->
        sla i (\ha ta -> slb i (\hb tb -> fc (fromPair (ha, hb)) (zip ta tb)))
    )

foldl :: (b -> a -> b) -> b -> SList a -> b
foldl f i (SList sl) = sl i (\h t -> foldl f (f i h) t)

foldr :: (a -> b -> b) -> b -> SList a -> b
foldr f i (SList sl) = sl i (\h t -> f h (foldr f i t))

take :: Int -> SList a -> SList a
take 0 _ = nilSL
take n (SList sl) = SList (\i fc -> sl i (\h t -> fc h (take (n - 1) t)))
