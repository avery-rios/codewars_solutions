{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module LispLovesMe (AST (..), lispEval, lispPretty) where

import Control.Applicative
import Data.Attoparsec.Text as Atto hiding (skipSpace, space)
import Data.Char (isDigit)
import Data.Foldable
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LTB
import qualified Data.Text.Lazy.Builder.Int as LTB

data AST
  = I32 Int
  | Sym String
  | Nul
  | Err
  | Lst [AST]
  | Boo Bool
  | Nod AST [AST]
  deriving (Eq, Show)

data Builtin
  = BPlus
  | BMul
  | BMinus
  | BDiv
  | BPow
  | BLt
  | BLe
  | BEq
  | BNe
  | BGe
  | BGt
  | BNot
  | BList
  | BSize
  | BReverse
  | BEnum
  | BIf
  deriving (Show)

builtinText :: Builtin -> Text
builtinText b =
  case b of
    BPlus -> "+"
    BMinus -> "-"
    BMul -> "*"
    BDiv -> "/"
    BPow -> "^"
    BLt -> "<"
    BLe -> "<="
    BEq -> "=="
    BNe -> "!="
    BGe -> ">="
    BGt -> ">"
    BNot -> "!"
    BList -> "list"
    BSize -> "size"
    BReverse -> "reverse"
    BEnum -> ".."
    BIf -> "if"

data Symbol
  = SBuiltin Builtin
  | SUser Text
  deriving (Show)

symbolText :: Symbol -> Text
symbolText (SBuiltin b) = builtinText b
symbolText (SUser t) = t

data ASTi
  = AInt Int
  | ASym Symbol
  | ANull
  | AList [ASTi]
  | ABool Bool
  | AError
  | ANode ASTi [ASTi]
  deriving (Show)

toAst :: ASTi -> AST
toAst (AInt i) = I32 i
toAst (ASym t) = Sym (T.unpack (symbolText t))
toAst ANull = Nul
toAst AError = Err
toAst (AList l) = Lst (fmap toAst l)
toAst (ABool b) = Boo b
toAst (ANode h t) = Nod (toAst h) (fmap toAst t)

isSpace :: Char -> Bool
isSpace c = c == ' ' || c == ',' || c == '\r' || c == '\n' || c == '\t'

skipSpace :: Parser ()
skipSpace = skipWhile isSpace

exprP :: Parser ASTi
exprP =
  choice
    [ AInt <$> signed decimal,
      ANull <$ string "null",
      ABool True <$ string "true",
      ABool False <$ string "false",
      char '('
        >> skipSpace
        >> (liftA2 ANode exprP (many (skipSpace >> exprP)) <|> pure ANull)
          <* skipSpace
          <* char ')',
      ASym . SBuiltin
        <$> choice
          ( fmap
              (\b -> b <$ string (builtinText b))
              [ BPlus,
                BMul,
                BMinus,
                BDiv,
                BPow,
                BLe, -- try <= before <
                BLt,
                BEq,
                BNe,
                BGe,
                BGt,
                BNot,
                BList,
                BSize,
                BReverse,
                BEnum,
                BIf
              ]
          ),
      ASym . SUser
        <$> liftA2
          T.cons
          (satisfy (\c -> not (isSpace c || c == '(' || c == ')' || isDigit c)))
          (Atto.takeWhile (\c -> not (isSpace c || c == '(' || c == ')')))
    ]

parseStr :: String -> Maybe ASTi
parseStr s = case parseOnly (skipSpace >> exprP <* skipSpace <* endOfInput) (T.pack s) of
  Right r -> Just r
  Left _ -> Nothing

arithFun :: (Int -> [Int] -> Int) -> [ASTi] -> ASTi
arithFun f as = case traverse
  ( \case
      AInt i -> Just i
      _ -> Nothing
  )
  as of
  Just (h : t) -> AInt (f h t)
  Just [] -> AError
  Nothing -> AError

cmpFun :: (Int -> Int -> Bool) -> [ASTi] -> ASTi
cmpFun f [AInt l, AInt r] = ABool (f l r)
cmpFun _ _ = AError

listFun :: ([ASTi] -> ASTi) -> [ASTi] -> ASTi
listFun f [AList l] = f l
listFun _ _ = AError

eval :: ASTi -> ASTi
eval (ANode h t) =
  let et = fmap eval t
   in case eval h of
        ASym (SBuiltin bt) -> case bt of
          BPlus -> arithFun (foldl' (+)) et
          BMinus -> arithFun (foldl' (-)) et
          BMul -> arithFun (foldl' (*)) et
          BDiv -> arithFun (foldl' div) et
          BPow -> case et of
            [AInt b, AInt e] -> AInt (b ^ e)
            _ -> AError
          BLt -> cmpFun (<) et
          BLe -> cmpFun (<=) et
          BEq -> cmpFun (==) et
          BNe -> cmpFun (/=) et
          BGe -> cmpFun (>=) et
          BGt -> cmpFun (>) et
          BNot -> case et of
            [ABool b] -> ABool (not b)
            _ -> AError
          BList -> AList et
          BSize -> listFun (AInt . length) et
          BReverse -> listFun (AList . reverse) et
          BEnum -> case et of
            [AInt a, AInt b] -> AList (AInt <$> [a .. b])
            _ -> AError
          BIf -> case et of
            [ABool True, a] -> a
            [ABool True, a, _] -> a
            [ABool False, _, b] -> b
            [ABool False, _] -> ANull
            _ -> AError
        _ -> AError
eval a = a

pretty :: ASTi -> LTB.Builder
pretty (AInt i) = LTB.decimal i
pretty (ASym t) = LTB.fromText (symbolText t)
pretty ANull = "null"
pretty AError = "error"
pretty (AList l) = pretty (ANode (ASym (SBuiltin BList)) l)
pretty (ABool b) = if b then "true" else "false"
pretty (ANode l e) = mconcat ["(", pretty l, foldMap' (\n -> " " <> pretty n) e, ")"]

lispPretty :: String -> Maybe String
lispPretty s = fmap (LT.unpack . LTB.toLazyText . pretty) (parseStr s)

lispEval :: String -> Maybe AST
lispEval s = fmap (toAst . eval) (parseStr s)
