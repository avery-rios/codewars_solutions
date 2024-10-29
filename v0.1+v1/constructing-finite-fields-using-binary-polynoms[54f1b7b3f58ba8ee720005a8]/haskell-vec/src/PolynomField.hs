module PolynomField
  ( BinaryPolynom,
    zero,
    one,
    deg,
    polyFromDeg,
    polyFromPowers,
    multiply,
    polyDivMod,
    (.+.),
    (.*.),
  )
where

import Control.Monad (when)
import Control.Monad.ST
import Data.Bits (Bits (xor))
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

-- | coeffient from low power to high, first is not zero
newtype BinaryPolynom = BinaryPolynom (VU.Vector Bool)
  deriving (Eq)

zero, one :: BinaryPolynom
zero = BinaryPolynom VU.empty
one = BinaryPolynom (VU.singleton True)

deg :: BinaryPolynom -> Int
deg (BinaryPolynom v) = VU.length v - 1

-- | Constructs a monom with the given degree.
polyFromDeg :: Int -> BinaryPolynom
polyFromDeg (-1) = zero
polyFromDeg i =
  BinaryPolynom
    ( VU.create
        ( do
            v <- VUM.replicate (i + 1) False
            VUM.unsafeWrite v i True
            pure v
        )
    )

fromPowers :: Int -> [Int] -> BinaryPolynom
fromPowers degree p =
  BinaryPolynom
    ( VU.create
        ( do
            v <- VUM.replicate (degree + 1) False
            iter v p
            pure v
        )
    )
  where
    iter _ [] = pure ()
    iter v (p0 : ps) = VUM.unsafeWrite v p0 True >> iter v ps

polyFromPowers :: [Int] -> BinaryPolynom
polyFromPowers [] = zero
polyFromPowers p = fromPowers (maximum p) p

instance Show BinaryPolynom where
  show (BinaryPolynom v) =
    case VU.findIndex id v of -- find first non zero
      Just 0 -> showP 1 "1" (VU.drop 1 v)
      Just p -> showP (p + 1) (showTerm p "") (VU.drop (p + 1) v)
      Nothing -> "0"
    where
      showTerm :: Int -> String -> String
      showTerm p s = 'x' : '^' : shows p s

      showP base =
        VU.ifoldl'
          ( \s p coeff ->
              if coeff
                then showTerm (base + p) (' ' : '+' : ' ' : s)
                else s
          )

stripZero :: VUM.MVector s Bool -> ST s (VUM.MVector s Bool)
stripZero v
  | VUM.null v = pure v
  | otherwise = do
      lastV <- VUM.unsafeRead v (VUM.length v - 1)
      if lastV
        then pure v
        else stripZero (VUM.unsafeInit v)

-- | Multiplication in the polynom ring.
multiply :: BinaryPolynom -> BinaryPolynom -> BinaryPolynom
multiply (BinaryPolynom p0) (BinaryPolynom p1) =
  BinaryPolynom
    ( VU.create
        ( do
            ret <- VUM.replicate (VU.length p0 + VU.length p1 - 1) False
            VU.imapM_
              ( \pow0 coeff0 ->
                  when
                    coeff0
                    ( VU.imapM_
                        ( \pow1 coeff1 ->
                            VUM.unsafeModify ret (`xor` coeff1) (pow0 + pow1)
                        )
                        p1
                    )
              )
              p0
            stripZero ret
        )
    )

polyDivMod :: BinaryPolynom -> BinaryPolynom -> (BinaryPolynom, BinaryPolynom)
polyDivMod (BinaryPolynom x) (BinaryPolynom y) =
  runST
    ( do
        (q, mr) <- VU.thaw x >>= iter []
        r <- VU.unsafeFreeze mr
        pure (polyFromPowers q, BinaryPolynom r)
    )
  where
    -- requires: v is greater than y
    minus :: Int -> VUM.MVector s Bool -> ST s (VUM.MVector s Bool)
    minus pow v = do
      VU.imapM_ (\i coeff -> VUM.unsafeModify v (`xor` coeff) (pow + i)) y
      stripZero v

    iter :: [Int] -> VUM.MVector s Bool -> ST s ([Int], VUM.MVector s Bool)
    iter quotDegs m
      | VUM.length m >= VU.length y =
          let highDeg = VUM.length m - VU.length y
           in minus highDeg m >>= iter (highDeg : quotDegs)
      | otherwise = pure (quotDegs, m)

polyM :: BinaryPolynom
polyM = fromPowers 8 [8, 4, 3, 1, 0]

-- | Addition and multiplication in the polynom field.
(.+.), (.*.) :: BinaryPolynom -> BinaryPolynom -> BinaryPolynom
BinaryPolynom x0 .+. BinaryPolynom y0 =
  let (x, y) = if VU.length x0 > VU.length y0 then (x0, y0) else (y0, x0)
   in snd
        ( polyDivMod
            ( BinaryPolynom
                ( VU.create
                    ( do
                        ret <- VU.thaw x
                        VU.imapM_ (\i vy -> VUM.unsafeModify ret (`xor` vy) i) y
                        stripZero ret
                    )
                )
            )
            polyM
        )
x .*. y = snd (polyDivMod (x `multiply` y) polyM)
