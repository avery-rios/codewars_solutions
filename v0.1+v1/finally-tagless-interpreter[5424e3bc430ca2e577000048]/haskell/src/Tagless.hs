{-# LANGUAGE RankNTypes #-}

module Tagless (Language (..), Term, interpret) where

import Prelude hiding (and, or)

class Language r where
  here :: r (a, h) a
  before :: r h a -> r (any, h) a
  lambda :: r (a, h) b -> r h (a -> b)
  apply :: r h (a -> b) -> (r h a -> r h b)

  loop :: r h (a -> a) -> r h a

  int :: Int -> r h Int
  add :: r h Int -> r h Int -> r h Int
  down :: r h Int -> r h Int -- \x -> x - 1
  up :: r h Int -> r h Int -- \x -> x + 1
  mult :: r h Int -> r h Int -> r h Int
  gte :: r h Int -> r h Int -> r h Bool -- greater than or equal

  bool :: Bool -> r h Bool
  and :: r h Bool -> r h Bool -> r h Bool
  or :: r h Bool -> r h Bool -> r h Bool
  neg :: r h Bool -> r h Bool

  ifte :: r h Bool -> r h a -> r h a -> r h a -- if true then return left term, else return right term

type Term a = forall r h. (Language r) => r h a

newtype R h t = R {unR :: h -> t}

instance Language R where
  here = R (\(v, _) -> v)
  before (R e) = R (\(_, f) -> e f)
  lambda (R e) = R (\env x -> e (x, env))
  apply (R e1) (R e2) = R (\env -> e1 env (e2 env))

  loop (R e) = R (\env -> let r = e env r in r)

  int i = R (const i)
  add (R e1) (R e2) = R (\env -> e1 env + e2 env)
  down (R e) = R (\env -> e env - 1)
  up (R e) = R (\env -> e env + 1)
  mult (R e1) (R e2) = R (\env -> e1 env * e2 env)
  gte (R e1) (R e2) = R (\env -> e1 env >= e2 env)

  bool b = R (const b)
  and (R e1) (R e2) = R (\env -> e1 env && e2 env)
  or (R e1) (R e2) = R (\env -> e1 env || e2 env)
  neg (R e) = R (not . e)

  ifte (R c) (R e1) (R e2) = R (\env -> if c env then e1 env else e2 env)

interpret :: Term a -> a
interpret t = unR t ()
