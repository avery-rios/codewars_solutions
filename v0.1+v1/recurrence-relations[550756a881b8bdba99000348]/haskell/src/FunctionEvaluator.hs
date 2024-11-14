{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}

module FunctionEvaluator (evaluateFunction) where

import Control.Monad.State.Strict
import qualified Data.Map.Strict as M

evaluateFunction :: forall a b. (Ord a) => (a -> Either b ([a], [b] -> b)) -> a -> b
evaluateFunction f n = evalState (eval n) M.empty
  where
    eval :: a -> State (M.Map a b) b
    eval a =
      gets (M.lookup a) >>= \case
        Just v -> pure v
        Nothing -> do
          r <- case f a of
            Left v -> pure v
            Right (as, fb) -> fb <$> traverse eval as
          modify' (M.insert a r)
          pure r
