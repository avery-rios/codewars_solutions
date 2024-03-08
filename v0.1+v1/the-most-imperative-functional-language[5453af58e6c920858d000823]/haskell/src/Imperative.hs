{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types #-}

module Imperative
  ( ImpM,
    Ref,
    Lit,
    AsValue,
    def,
    var,
    lit,
    while,
    (+=),
    (-=),
    (*=),
  )
where

import Control.Monad
import Control.Monad.ST.Strict
import Data.STRef.Strict

newtype ImpM s a = ImpM {runImpM :: ST s a}
  deriving (Functor, Applicative, Monad)

newtype Ref s = Ref (STRef s Integer)

newtype Lit s = Lit Integer

class AsValue a where
  asValue :: a s -> ST s Integer

instance AsValue Ref where
  asValue (Ref r) = readSTRef r

instance AsValue Lit where
  asValue (Lit v) = pure v

def :: (AsValue a) => (forall s. ImpM s (a s)) -> Integer
def m = runST (runImpM m >>= asValue)

var :: Integer -> ImpM s (Ref s)
var v = ImpM (Ref <$> newSTRef v)

lit :: Integer -> Lit s
lit = Lit

while :: Ref s -> (Integer -> Bool) -> ImpM s a -> ImpM s ()
while (Ref r) f (ImpM act) = ImpM run
  where
    run =
      readSTRef r >>= \vr ->
        when (f vr) $ act >> run

(+=) :: (AsValue b) => Ref s -> b s -> ImpM s ()
Ref a += b = ImpM (asValue b >>= \v -> modifySTRef' a (+ v))

(-=) :: (AsValue b) => Ref s -> b s -> ImpM s ()
Ref a -= b = ImpM (asValue b >>= \v -> modifySTRef' a (\va -> va - v))

(*=) :: (AsValue b) => Ref s -> b s -> ImpM s ()
Ref a *= b = ImpM (asValue b >>= \v -> modifySTRef' a (* v))
