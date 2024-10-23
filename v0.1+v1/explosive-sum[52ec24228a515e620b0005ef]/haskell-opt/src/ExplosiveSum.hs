{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE Strict #-}

module ExplosiveSum (explosiveSum) where

import Control.Monad (forM_)
import qualified Data.Vector.Primitive as V
import qualified Data.Vector.Primitive.Mutable as VM
import Data.Word (Word64)

createTable :: Int -> V.Vector Word64
createTable n =
  V.create
    ( do
        mat <- VM.replicate (n + 1) 1
        forM_ [2 .. n] \i ->
          forM_ [i .. n] \j ->
            VM.unsafeRead mat (j - i) >>= \v ->
              VM.unsafeModify mat (v +) j
        pure mat
    )

explosiveSum :: Integer -> Integer
explosiveSum n =
  let wn = fromIntegral n :: Int
   in fromIntegral (V.unsafeIndex (createTable wn) wn)
