{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Transpiler (transpile) where

import Control.Applicative (optional)
import Control.Monad (void, when)
import Data.Attoparsec.Text
import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LTB
import Data.Vector (Vector)
import qualified Data.Vector as V

newtype NameOrNum = NameOrNum Text
  deriving (Show)

data Lambda = Lambda
  { lamParam :: Vector NameOrNum,
    lamStmt :: Vector NameOrNum
  }
  deriving (Show)

data Expr = ENameOrNum NameOrNum | ELam Lambda
  deriving (Show)

data Function = Function
  { fFun :: Expr,
    fParam :: Vector Expr,
    fLambda :: Maybe Lambda
  }
  deriving (Show)

nameOrNumP :: Parser NameOrNum
nameOrNumP =
  peekChar' >>= \c ->
    if isDigit c
      then
        NameOrNum
          <$> takeWhile1 isDigit
          <* ( peekChar' >>= \n ->
                 when (isAlpha n || n == '_') (fail "invalid name")
             )
      else NameOrNum <$> takeWhile1 (\c1 -> isAlphaNum c1 || c1 == '_')

nameOrNumR :: NameOrNum -> LTB.Builder
nameOrNumR (NameOrNum v) = LTB.fromText v

lambdaP :: Parser Lambda
lambdaP = do
  char '{' >> skipSpace
  params <-
    optional
      ( sepBy1' (nameOrNumP <* skipSpace) (char ',' >> skipSpace)
          <* string "->"
      )
  skipSpace
  stmts <- many' (nameOrNumP <* skipSpace)
  void (char '}')
  pure
    Lambda
      { lamParam = maybe V.empty V.fromList params,
        lamStmt = V.fromList stmts
      }

lambdaR :: Lambda -> LTB.Builder
lambdaR l =
  ( "("
      <> ( case V.uncons (lamParam l) of
             Just (h, t) ->
               nameOrNumR h
                 <> V.foldl' (\m v -> m <> "," <> nameOrNumR v) mempty t
             Nothing -> mempty
         )
      <> ")"
  )
    <> ( "{"
           <> V.foldl'
             (\m v -> m <> nameOrNumR v <> ";")
             mempty
             (lamStmt l)
           <> "}"
       )

exprP :: Parser Expr
exprP =
  peekChar' >>= \case
    '{' -> ELam <$> lambdaP
    _ -> ENameOrNum <$> nameOrNumP

exprR :: Expr -> LTB.Builder
exprR (ENameOrNum n) = nameOrNumR n
exprR (ELam l) = lambdaR l

functionP :: Parser Function
functionP = do
  fun <- exprP <* skipSpace
  param <-
    maybe V.empty V.fromList
      <$> optional
        ( do
            char '(' >> skipSpace
            params <- sepBy' (exprP <* skipSpace) (char ',' >> skipSpace)
            skipSpace
            void (char ')')
            pure params
        )
  skipSpace
  lam <- optional lambdaP
  pure
    Function
      { fFun = fun,
        fParam = param,
        fLambda = lam
      }

functionR :: Function -> LTB.Builder
functionR f =
  exprR (fFun f)
    <> "("
    <> ( case (V.uncons (fParam f), fLambda f) of
           (Just (h, t), l) ->
             exprR h
               <> V.foldl' (\m e -> m <> "," <> exprR e) mempty t
               <> maybe mempty (\lam -> "," <> lambdaR lam) l
           (Nothing, Just l) -> lambdaR l
           (Nothing, Nothing) -> mempty
       )
    <> ")"

parser :: Parser Function
parser = skipSpace >> functionP <* skipSpace <* endOfInput

transpile :: String -> Either String String
transpile s = case parseOnly parser (T.pack s) of
  Right f -> Right (LT.unpack (LTB.toLazyText (functionR f)))
  Left _ -> Left "Hugh?"
