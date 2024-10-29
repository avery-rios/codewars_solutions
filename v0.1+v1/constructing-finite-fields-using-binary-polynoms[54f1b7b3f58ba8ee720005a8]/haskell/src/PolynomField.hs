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

import Data.Bits
import Data.Foldable (Foldable (foldl'))
import Data.Word (Word32)

-- | coeffient from low power to high, first is not zero
newtype BinaryPolynom = BinaryPolynom Word32
  deriving (Eq)

zero, one :: BinaryPolynom
zero = BinaryPolynom 0
one = BinaryPolynom 1

deg :: BinaryPolynom -> Int
deg (BinaryPolynom pv) = finiteBitSize pv - 1 - countLeadingZeros pv

-- | Constructs a monom with the given degree.
polyFromDeg :: Int -> BinaryPolynom
polyFromDeg (-1) = zero
polyFromDeg i = BinaryPolynom (1 `shiftL` i)

polyFromPowers :: [Int] -> BinaryPolynom
polyFromPowers p = BinaryPolynom (foldl' setBit 0 p)

foldTerml :: (Int -> a -> a) -> a -> Word32 -> a
foldTerml f = iter 0
  where
    iter _ acc 0 = acc
    iter base acc i
      | i .&. 1 == 1 = iter (base + 1) (f base acc) (i `unsafeShiftR` 1)
      | otherwise = iter (base + 1) acc (i `unsafeShiftR` 1)

instance Show BinaryPolynom where
  show (BinaryPolynom 0) = "0"
  show (BinaryPolynom pv) =
    case countTrailingZeros pv of -- find first non zero
      0 -> showP 1 (pv `shiftR` 1) "1"
      p -> showP (p + 1) (pv `unsafeShiftR` (p + 1)) (showTerm p "")
    where
      showTerm :: Int -> String -> String
      showTerm p s = 'x' : '^' : shows p s

      showP :: Int -> Word32 -> String -> String
      showP base v s =
        foldTerml (\pos str -> showTerm (base + pos) (' ' : '+' : ' ' : str)) s v

-- | Multiplication in the polynom ring.
multiply :: BinaryPolynom -> BinaryPolynom -> BinaryPolynom
multiply (BinaryPolynom p0) (BinaryPolynom p1) =
  BinaryPolynom (foldTerml (\pos acc -> acc `xor` (p1 `unsafeShiftL` pos)) 0 p0)

polyDivMod :: BinaryPolynom -> BinaryPolynom -> (BinaryPolynom, BinaryPolynom)
polyDivMod (BinaryPolynom x) py@(BinaryPolynom y) = iter 0 x
  where
    degY = deg py

    iter q m =
      let degM = deg (BinaryPolynom m)
       in if degM >= degY
            then
              let highPow = degM - degY
               in iter (setBit q highPow) (m `xor` (y `unsafeShiftL` highPow))
            else (BinaryPolynom q, BinaryPolynom m)

polyM :: BinaryPolynom
polyM = polyFromPowers [8, 4, 3, 1, 0]

-- | Addition and multiplication in the polynom field.
(.+.), (.*.) :: BinaryPolynom -> BinaryPolynom -> BinaryPolynom
BinaryPolynom x .+. BinaryPolynom y =
  snd (polyDivMod (BinaryPolynom (x `xor` y)) polyM)
x .*. y = snd (polyDivMod (x `multiply` y) polyM)
