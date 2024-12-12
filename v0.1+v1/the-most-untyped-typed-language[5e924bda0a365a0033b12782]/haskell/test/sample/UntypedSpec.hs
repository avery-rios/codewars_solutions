module UntypedSpec where
import Prelude hiding (pred,and,or)
import Untyped
import Test.Hspec
import Test.QuickCheck

from :: Int -> D
from x = N $ from' x
    where
        from' x = if x <= 0 then O else S $ from' (x - 1)
main = hspec spec
spec = do
  describe "plus" $ do
    it "x+x=2x" $ do
      property $ \(NonNegative x) ->
          let a = fromPeano (from x) :: D
              a' = fromPeano (from (2 * x)) :: D
          in showPeano (toPeano (plus `app` a `app` a)) == showPeano (toPeano a')
    it "suc 0 = 1" $ do
        (showPeano (toPeano (suc `app` zero)) == 1) &&
            ((showPeano (toPeano one)) == 1)
  describe "mult" $ do
    it "comm" $ do
        property $ \(NonNegative x, NonNegative y) ->
          let x' = fromPeano (from x) :: D
              y' = fromPeano (from y) :: D
          in showPeano (toPeano (mult `app` x' `app` y')) == showPeano (toPeano (mult `app` y' `app` x'))
    it "assoc" $ do
        property $ \(Small x, Small y, Small z) ->
          let x' = fromPeano (from x) :: D
              y' = fromPeano (from y) :: D
              z' = fromPeano (from z) :: D
              xy_z = mult `app` (mult `app` x' `app` y') `app` z'
              x_yz = mult `app` x' `app` (mult `app` y' `app` z')
          in showPeano (toPeano xy_z) == showPeano (toPeano x_yz)
    it "0x=0" $ do
        property $ \(NonNegative x) ->
          let x' = fromPeano (from x) :: D
          in showPeano (toPeano (mult `app` zero `app` x')) == showPeano (toPeano zero)
    it "1x=x" $ do
        property $ \(NonNegative x) ->
          let x' = fromPeano (from x) :: D
          in showPeano (toPeano (mult `app` one `app` x')) == showPeano (toPeano x')
  describe "pred" $ do
    it "pred (x+1) = x" $ do 
        property $ \(NonNegative x) ->
          let x' = fromPeano (from $ x+1) :: D
          in showPeano (toPeano (pred `app` x')) == x
  describe "ycomb & cond" $ do
    it "fib" $ do
        let fun = lam $ \self -> lam $ \x ->
                ite `app` (or `app` (iszero `app` x) `app` (iszero `app` (pred `app` x))) `app`
                    one `app`
                    (plus `app` (self `app` (pred `app` x))
                        `app` (self `app` (pred `app` (pred `app` x))))
        let fun' = ycomb `app` fun
        let fibs = 1 : 1 : zipWith (+) fibs (tail fibs)
        all id $ fmap (\x ->
            let x' = fromPeano (from x) :: D
            in showPeano (toPeano (fun' `app` x')) == fibs !! x) [0..12]
    it "fact" $ do
        let fun = lam $ \self -> lam $ \x ->
                ite `app` (iszero `app` x) `app`
                    one `app`
                    (mult `app` x `app` (self `app` (pred `app` x)))
        let fun' = ycomb `app` fun
        let facts = 1 : zipWith (*) [1..] facts
        all id $ fmap (\x ->
            let x' = fromPeano (from x) :: D
            in showPeano (toPeano (fun' `app` x')) == facts !! x) [0..8]
      