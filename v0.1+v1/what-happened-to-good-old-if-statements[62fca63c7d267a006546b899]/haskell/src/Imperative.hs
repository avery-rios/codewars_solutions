{-
  We need BlockArguments for a bit nicer syntax in our imperative code.

  With BlockArguments:              Without BlockArguments:
  while a (<) 3 do                  while a (<) 3 $ do
    ...                               ...

  We need RebindableSyntax because we rewrite (>>=), (>>) and return,
  but still want to use do-notation.
-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- you might not need this once you have defined all types, it prevents inference errors in the initial solution
{-# LANGUAGE NoPolyKinds #-}

module Imperative where

import Control.Monad.ST
import Data.Functor
import Data.STRef
import Prelude hiding (return, (>>), (>>=))
import qualified Prelude as P

-- to implement mutable state we will use the ST monad
-- our variables will be STRefs accordingly
type Var = STRef

-- Imperative will be our main type that our imperative operations run it.
-- It takes a state of type `before` and returns a state of type `after`.
-- This will get used once we get to if/elif/else
-- The `st` type will be needed by the ST monad.

-- you will need to complete this type definition
newtype Imperative st before after a = Imperative {runImp :: before -> ST st (a, after)}

-- Compare this to the type definition of Preludes (>>=).
-- Why can't we make `Imperative` a monad and use Preludes (>>=)?
(>>=) :: Imperative st s t a -> (a -> Imperative st t u b) -> Imperative st s u b
(>>=) (Imperative ma) f = Imperative (\s0 -> ma s0 P.>>= \(a, s1) -> runImp (f a) s1)

-- We could generalize (>>=)/(>>)/return to work on anything that
-- is known as an 'indexed monad' (we don't do that here though).
(>>) :: Imperative st p q a -> Imperative st q r b -> Imperative st p r b
(>>) (Imperative ma) (Imperative mb) = Imperative (\s0 -> ma s0 P.>>= \(_, s1) -> mb s1)

return :: a -> Imperative st s s a
return v = Imperative (\s -> pure (v, s))

def :: (forall st. Imperative st NothingYet s (Var st a)) -> a
def m = runST (runImp m NothingYet P.>>= \(v, _) -> readSTRef v)

var :: a -> Imperative st s s (Var st a)
var v = Imperative (\s -> (,s) <$> newSTRef v)

-- Now it's time to make use of our state.
-- We use these two types to prohibit invalid uses of elif/else.
-- Invalid examples: two consecutive elses, elif without an if before it
data NothingYet = NothingYet

data SawIf = SawIfRun | SawIfNotRun

{-
  Next, let's introduce a new typeclass so that we can use
  variables and values interchangeably in certain places.

  a <- var 1
  a += 1 -- add a variable and a value
  a += a -- add a variable and a variable

  b <- var 2
  if a (<) b do -- compare variable with a variable
    ...
  if a (<) 2 do -- compare a variable with a value
    ...
  while 1 (<) 2 do -- compare a value with a value
    ...
-}
class HasValue st a b where
  getValue :: forall s. a -> Imperative st s s b

instance {-# OVERLAPPING #-} (a ~ b) => HasValue st (Var st a) b where
  getValue v = Imperative (\s0 -> (,s0) <$> readSTRef v)

instance (a ~ b) => HasValue st a b where
  getValue = return

while :: (HasValue st v a, HasValue st w b) => v -> (a -> b -> Bool) -> w -> Imperative st s t r -> Imperative st s s ()
while v f c b = do
  vv <- getValue v
  vc <- getValue c
  case f vv vc of
    True -> Imperative (\s0 -> runImp b s0 P.>> runImp (while v f c b) s0)
    False -> return ()

if' :: (HasValue st v a, HasValue st w b) => v -> (a -> b -> Bool) -> w -> Imperative st s s r -> Imperative st s SawIf ()
if' v f c b = do
  vv <- getValue v
  vc <- getValue c
  case f vv vc of
    True -> b >> Imperative (\_ -> pure ((), SawIfRun))
    False -> Imperative (\_ -> pure ((), SawIfNotRun))

elif' :: (HasValue st v a, HasValue st w b) => v -> (a -> b -> Bool) -> w -> Imperative st SawIf s r -> Imperative st SawIf SawIf ()
elif' v f c b =
  Imperative (\s -> pure (s, s)) >>= \case
    SawIfRun -> Imperative (\_ -> pure ((), SawIfRun))
    SawIfNotRun -> do
      vv <- getValue v
      vc <- getValue c
      case f vv vc of
        True -> b >> Imperative (\_ -> pure ((), SawIfRun))
        False -> Imperative (\_ -> pure ((), SawIfNotRun))

else' :: Imperative st SawIf s b -> Imperative st SawIf NothingYet ()
else' (Imperative b) = Imperative \case
  SawIfRun -> pure ((), NothingYet)
  SawIfNotRun -> ((), NothingYet) <$ b SawIfNotRun

assignOP :: (HasValue st a t1) => (t2 -> t1 -> t2) -> Var st t2 -> a -> Imperative st u u ()
assignOP f v val =
  getValue val >>= \va ->
    Imperative (\s -> (,s) <$> modifySTRef' v (\old -> f old va))

(+=) :: (HasValue st a1 a2, Num a2) => Var st a2 -> a1 -> Imperative st u u ()
(+=) = assignOP (+)

(-=) :: (HasValue st a1 a2, Num a2) => Var st a2 -> a1 -> Imperative st u u ()
(-=) = assignOP (-)

(*=) :: (HasValue st a1 a2, Num a2) => Var st a2 -> a1 -> Imperative st u u ()
(*=) = assignOP (*)

(.=) :: (HasValue st a1 a2) => STRef st a2 -> a1 -> Imperative st u u ()
(.=) v val = getValue val >>= \va -> Imperative (\s -> (,s) <$> writeSTRef v va)

push :: (HasValue st a l) => Var st [l] -> a -> Imperative st u u ()
push = assignOP (\l t -> l ++ [t])

toString :: (Show a) => STRef st a -> Imperative st u u String
toString v = Imperative (\s -> fmap (\va -> (show va, s)) (readSTRef v))
