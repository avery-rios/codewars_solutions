{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}

module EvaluateMathematicalExpression (Expr (..), parseExpr, calc) where

import Control.Applicative
import Data.Attoparsec.Text
import qualified Data.Text as T

data Expr
  = ELit Double
  | ENegate Expr
  | EAdd Expr Expr
  | EMinus Expr Expr
  | ETimes Expr Expr
  | EDiv Expr Expr
  deriving (Show)

class ExprV a where
  lit :: Double -> a
  neg :: a -> a
  add :: a -> a -> a
  minus :: a -> a -> a
  times :: a -> a -> a
  divide :: a -> a -> a

instance ExprV Expr where
  lit = ELit
  neg = ENegate
  add = EAdd
  minus = EMinus
  times = ETimes
  divide = EDiv

instance ExprV Double where
  lit i = i
  neg i = -i
  add = (+)
  minus = (-)
  times = (*)
  divide = (/)

term :: (ExprV e) => Parser e
term =
  peekChar' >>= \case
    '-' -> neg <$> (char '-' >> term)
    '(' -> char '(' >> skipSpace >> expr <* skipSpace <* char ')'
    _ -> lit <$> double
{-# INLINEABLE term #-}

operE :: forall a. Parser (a -> a -> a) -> Parser a -> Parser a
operE op ex = ex >>= f
  where
    f :: a -> Parser a
    f l =
      ( try
          ( do
              skipSpace
              o <- op
              skipSpace
              o l <$> ex
          )
          >>= f
      )
        <|> pure l
{-# INLINEABLE operE #-}

productE :: (ExprV e) => Parser e
productE = operE ((times <$ char '*') <|> (divide <$ char '/')) term
{-# INLINEABLE productE #-}

expr :: (ExprV e) => Parser e
expr = operE ((add <$ char '+') <|> (minus <$ char '-')) productE
{-# INLINEABLE expr #-}

rootE :: (ExprV e) => Parser e
rootE = skipSpace >> (expr <* skipSpace)
{-# INLINEABLE rootE #-}

parseExpr :: String -> Either String Expr
parseExpr s = parseOnly rootE (T.pack s)

calc :: String -> Double
calc s = case parseOnly rootE (T.pack s) of
  Right e -> e
  Left e -> error e
