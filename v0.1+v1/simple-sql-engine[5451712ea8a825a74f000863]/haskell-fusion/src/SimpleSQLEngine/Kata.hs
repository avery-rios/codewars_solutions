{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module SimpleSQLEngine.Kata (Query, parseSql, sqlEngine) where

import Control.Applicative
import Data.Attoparsec.Text
import Data.Char (isAlphaNum)
import Data.Foldable
import Data.Functor
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Bundle as B
import qualified Data.Vector.Generic as VG

newtype TableName = TName Text
  deriving (Show, Eq, Hashable)

newtype ColumnName = CName Text
  deriving (Show, Eq, Hashable)

data ColumnId = ColumnId {ciTable :: TableName, ciColumn :: ColumnName}
  deriving (Show)

data Value = VConst Text | VColumn ColumnId
  deriving (Show)

data ValueComp
  = VcEq
  | VcGt
  | VcLt
  | VcLe
  | VcGe
  | VcNe
  deriving (Show)

data ValueTest = ValTest Value ValueComp Value
  deriving (Show)

data Join = Join TableName ValueTest
  deriving (Show)

data From = From TableName (V.Vector Join)
  deriving (Show)

type Select = V.Vector ColumnId

data Query = Query
  { qSelect :: Select,
    qFrom :: From,
    qWhere :: Maybe ValueTest
  }
  deriving (Show)

nameP :: Parser Text
nameP = takeWhile1 (\c -> c == '_' || isAlphaNum c)

tableNameP :: Parser TableName
tableNameP = TName <$> nameP

columnNameP :: Parser ColumnName
columnNameP = CName <$> nameP

columnIdP :: Parser ColumnId
columnIdP = liftA2 ColumnId tableNameP (char '.' >> columnNameP)

stringP :: Parser Text
stringP = do
  void (char '\'')
  cs <-
    many1
      ( peekChar' >>= \case
          '\'' -> '\'' <$ string "''"
          _ -> anyChar
      )
  void (char '\'')
  pure (T.pack cs)

valueP :: Parser Value
valueP =
  peekChar' >>= \case
    '\'' -> VConst <$> stringP
    _ -> VColumn <$> columnIdP

keyword :: Text -> Parser ()
keyword t = asciiCI t >> skipSpace

valueTestP :: Parser ValueTest
valueTestP =
  liftA3
    ValTest
    (valueP <* skipSpace)
    ( choice
        [ VcEq <$ string "=",
          VcNe <$ string "<>",
          VcLe <$ string "<=",
          VcGe <$ string ">=",
          VcGt <$ string ">",
          VcLt <$ string "<"
        ]
    )
    (skipSpace >> valueP)

joinP :: Parser Join
joinP =
  keyword "JOIN"
    >> liftA2
      Join
      tableNameP
      (skipSpace >> keyword "on" >> valueTestP)

fromP :: Parser From
fromP =
  keyword "FROM"
    >> liftA2
      From
      tableNameP
      (V.fromList <$> many (skipSpace >> joinP))

queryP :: Parser Query
queryP = do
  skipSpace
  keyword "SELECT"
  cs <- V.fromList <$> sepBy1 (skipSpace >> columnIdP <* skipSpace) (char ',')
  f <- fromP <* skipSpace
  w <- optional (keyword "WHERE" >> valueTestP)
  pure Query {qSelect = cs, qFrom = f, qWhere = w}

parseSql :: Text -> Either String Query
parseSql = parseOnly queryP

type Row = HM.HashMap ColumnName Text

type Table = V.Vector Row

tableFromList :: [[(String, String)]] -> Table
tableFromList =
  V.fromList
    . fmap (HM.fromList . fmap (\(c, v) -> (CName (T.pack c), T.pack v)))

type Database = HM.HashMap TableName Table

type JoinedRow = HM.HashMap TableName Row

evalValue :: Value -> JoinedRow -> Maybe Text
evalValue (VConst c) _ = Just c
evalValue (VColumn c) j = HM.lookup (ciTable c) j >>= HM.lookup (ciColumn c)

evalTest :: ValueTest -> JoinedRow -> Bool
evalTest (ValTest vl c vr) jr =
  fromMaybe
    False
    ( liftA2
        ( \l r -> case c of
            VcEq -> l == r
            VcGt -> l > r
            VcLt -> l < r
            VcLe -> l <= r
            VcGe -> l >= r
            VcNe -> l /= r
        )
        (evalValue vl jr)
        (evalValue vr jr)
    )

data ResultCell = RCell ColumnId Text

type ResultRow = V.Vector ResultCell

resultRowToList :: ResultRow -> [(String, String)]
resultRowToList =
  V.toList
    . V.map
      ( \(RCell (ColumnId (TName tn) (CName cn)) v) ->
          ( T.unpack (tn <> "." <> cn),
            T.unpack v
          )
      )

evalSelect :: Select -> JoinedRow -> Maybe ResultRow
evalSelect s jr =
  traverse
    (\ci@(ColumnId t c) -> RCell ci <$> (HM.lookup t jr >>= HM.lookup c))
    s

evalJoin :: Database -> Join -> B.Bundle V.Vector JoinedRow -> B.Bundle V.Vector JoinedRow
evalJoin db (Join tName vt) jrs =
  case HM.lookup tName db of
    Just rs ->
      B.concatMap
        ( \jr ->
            B.mapMaybeM
              ( \r ->
                  let jr1 = HM.insertWith HM.union tName r jr
                   in if evalTest vt jr1 then pure (Just jr1) else pure Nothing
              )
              (VG.stream rs)
        )
        jrs
    Nothing -> B.empty

execute :: Database -> Query -> B.Bundle V.Vector ResultRow
execute db q@Query {qFrom = From tbl js} =
  B.concatMap
    ( \r ->
        B.mapMaybeM
          (pure . evalSelect (qSelect q))
          ( let jrs =
                  foldl'
                    (\jr j -> evalJoin db j jr)
                    (B.singleton (HM.singleton tbl r))
                    js
             in case qWhere q of
                  Just vt -> B.filter (evalTest vt) jrs
                  Nothing -> jrs
          )
    )
    (VG.stream (HM.lookupDefault V.empty tbl db))

mkDatabase :: [(String, [[(String, String)]])] -> Database
mkDatabase db =
  HM.fromList
    ( fmap
        (\(d, rs) -> (TName (T.pack d), tableFromList rs))
        db
    )

sqlEngine :: [(String, [[(String, String)]])] -> String -> [[(String, String)]]
sqlEngine database query = case parseSql (T.pack query) of
  Right sq ->
    B.toList
      ( B.map
          resultRowToList
          (execute (mkDatabase database) sq)
      )
  Left _ -> []
