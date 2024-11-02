{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE TemplateHaskell #-}

module Kata.TimesComm.TestSpec where

import Kata.TimesComm
import Kata.TimesComm.Definitions

import Test.Hspec
import Test.Hspec.Codewars

-- | Verify that the functions' signature is correct:
solution :: Natural a -> Natural b -> Equal (a :*: b) (b :*: a)
solution = timesComm

spec :: Spec
spec = do
  describe "Proof checking" $ do
    it "Doesn't use any unsafe modules" $
      solutionShouldHideAll [Module "Unsafe.Coerce"]
