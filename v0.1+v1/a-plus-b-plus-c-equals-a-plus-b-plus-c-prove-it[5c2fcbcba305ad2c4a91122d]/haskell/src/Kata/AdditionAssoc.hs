{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Kata.AdditionAssoc (plusAssoc) where

import Data.Type.Equality
import Kata.AdditionAssoc.Definitions

-- | For any n, n = n.
reflexive :: Natural n -> Equal n n
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS (reflexive n)

plusN :: Natural a -> Natural b -> Natural (a :+: b)
plusN NumZ b = b
plusN (NumS a) b = NumS (plusN a b)

plusAssocE :: Natural a -> Natural b -> Natural c -> (a :+: (b :+: c)) :~: ((a :+: b) :+: c)
plusAssocE NumZ _ _ = Refl
plusAssocE (NumS a) b c =
  case plusAssocE a b c of
    Refl -> Refl

-- | a + (b + c) = (a + b) + c
plusAssoc :: Natural a -> Natural b -> Natural c -> Equal (a :+: (b :+: c)) ((a :+: b) :+: c)
plusAssoc a b c = case plusAssocE a b c of
  Refl -> reflexive (plusN (plusN a b) c)
