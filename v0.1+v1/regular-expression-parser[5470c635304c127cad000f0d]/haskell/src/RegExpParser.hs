module RegExpParser (RegExp (..), parseRegExp) where

import Control.Applicative
import Data.Attoparsec.Text
import Data.Foldable
import qualified Data.Text as T

data RegExp
  = -- | A character that is not in "()*|."
    Normal Char
  | -- | Any character
    Any
  | -- | Zero or more occurances of the same regexp
    ZeroOrMore RegExp
  | -- | A choice between 2 regexps
    Or RegExp RegExp
  | -- | A sequence of regexps.
    Str [RegExp]
  deriving (Show, Eq)

elemP :: Parser RegExp
elemP =
  choice
    [ Any <$ char '.',
      char '(' >> exprP <* char ')',
      Normal <$> satisfy (`notElem` "().|*")
    ]

starP :: Parser RegExp
starP =
  liftA2
    ( \e c ->
        case c of
          Just _ -> ZeroOrMore e
          Nothing -> e
    )
    elemP
    (optional (char '*'))

seqP :: Parser RegExp
seqP =
  liftA2
    ( \h t -> case t of
        [] -> h
        _ -> Str (h : t)
    )
    starP
    (many starP)

exprP :: Parser RegExp
exprP = liftA2 (foldl' Or) seqP (many (char '|' >> seqP))

parseRegExp :: String -> Maybe RegExp
parseRegExp s =
  case parseOnly (exprP <* endOfInput) (T.pack s) of
    Right e -> Just e
    Left _ -> Nothing
