{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ApplicativeParser where

import Data.Bifunctor
import Data.Char
import qualified Data.List as L
import Data.Maybe
import Prelude hiding (fmap)

-- | An ambiguous parser.
newtype Parser a = P {unP :: String -> [(String, a)]}

-- | Change the result of a parser.
pmap :: (a -> b) -> Parser a -> Parser b
pmap f (P p) = P (map (second f) . p)

-- | Operator version of 'pmap'.
(<#>) :: (a -> b) -> Parser a -> Parser b
(<#>) = pmap

-- | Parse a value and replace it.
(<#) :: a -> Parser b -> Parser a
(<#) v (P p) = P (map (\(r, _) -> (r, v)) . p)

infixl 4 <#>

infixl 4 <#

-- | Parse a character only when a predicate matches.
predP :: (Char -> Bool) -> Parser Char
predP p = P \case
  h : t | p h -> [(t, h)]
  _ -> []

-- | Succeed only when parsing the given character.
charP :: Char -> Parser Char
charP c = P \case
  h : t | c == h -> [(t, c)]
  _ -> []

-- | Inject a value into an identity parser.
inject :: a -> Parser a
inject x = P (\i -> [(i, x)])

-- | Given a parser with a function value and another parser, parse the function
-- first and then the value, return a parser which applies the function to the
-- value.
(<@>) :: Parser (a -> b) -> Parser a -> Parser b
P pf <@> P px = P (concatMap (\(r, f) -> map (second f) (px r)) . pf)

(<@) :: Parser a -> Parser b -> Parser a
P pa <@ P pb = P (concatMap (\(r, va) -> map (\(rb, _) -> (rb, va)) (pb r)) . pa)

(@>) :: Parser a -> Parser b -> Parser b
P pa @> P pb = P (concatMap (\(r, _) -> pb r) . pa)

infixl 4 <@

infixl 4 @>

infixl 4 <@>

-- | Parse a whole string.
stringP :: String -> Parser String
stringP s = P \i ->
  case L.stripPrefix s i of
    Just r -> [(r, i)]
    Nothing -> []

-- | Construct a parser that never parses anything.
emptyP :: Parser a
emptyP = P (const [])

-- | Combine two parsers: When given an input, provide the results of both parser run on the input.
(<<>>) :: Parser a -> Parser a -> Parser a
(<<>>) (P pa) (P pb) = P (\i -> pa i ++ pb i)

infixl 3 <<>>

-- | Apply the parser zero or more times.
many :: forall a. Parser a -> Parser [a]
many p = some p <<>> inject []

-- | Apply the parser one or more times.
some :: Parser a -> Parser [a]
some p = inject (:) <@> p <@> many p

-- | Apply a parser and return all ambiguous results, but only those where the input was fully consumed.
runParser :: Parser a -> String -> [a]
runParser (P p) cs =
  mapMaybe
    ( \case
        ([], r) -> Just r
        _ -> Nothing
    )
    (p cs)

-- | Apply a parser and only return a result, if there was only one unambiguous result with output fully consumed.
runParserUnique :: Parser a -> String -> Maybe a
runParserUnique p cs = case runParser p cs of
  [r] -> Just r
  _ -> Nothing

-- | Kinds of binary operators.
data BinOp = AddBO | MulBO deriving (Eq, Show)

-- | Some kind of arithmetic expression.
data Expr
  = ConstE Int
  | BinOpE BinOp Expr Expr
  | NegE Expr
  | ZeroE
  deriving (Eq, Show)

evalExpr :: Expr -> Int
evalExpr (ConstE i) = i
evalExpr (BinOpE op el er) =
  let vl = evalExpr el
      vr = evalExpr er
   in case op of
        AddBO -> vl + vr
        MulBO -> vl * vr
evalExpr (NegE e) = -(evalExpr e)
evalExpr ZeroE = 0

-- | Parse arithmetic expressions, with the following grammar:
--
--     expr         ::= const | binOpExpr | neg | zero
--     const        ::= int
--     binOpExpr    ::= '(' expr ' ' binOp ' ' expr ')'
--     binOp        ::= '+' | '*'
--     neg          ::= '-' expr
--     zero         ::= 'z'
parseExpr :: String -> Maybe Expr
parseExpr = runParserUnique expr
  where
    expr :: Parser Expr
    expr =
      pmap (ConstE . read) (some (predP isDigit))
        <<>> ( charP '('
                 @> ( inject (\l o r -> BinOpE o l r)
                        <@> expr
                        <@> (AddBO <# stringP " + " <<>> MulBO <# stringP " * ")
                        <@> expr
                    )
                 <@ charP ')'
             )
        <<>> (charP '-' @> pmap NegE expr)
        <<>> (ZeroE <# stringP "z")
