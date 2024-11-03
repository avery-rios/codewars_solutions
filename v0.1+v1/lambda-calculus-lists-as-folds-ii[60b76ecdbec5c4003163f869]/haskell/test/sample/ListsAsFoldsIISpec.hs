{-# OPTIONS_GHC -O0 #-}

module ListsAsFoldsIISpec (spec) where

import Control.Exception (evaluate)
import Control.Monad (guard, unless, void)
import Data.Bool (bool)
import Data.Char (isDigit, isLetter)
import Data.Foldable (for_)
import ListsAsFolds (nil)
import qualified ListsAsFolds as L
  ( all,
    any,
    append,
    concat,
    cons,
    cycle,
    drop,
    filter,
    find,
    findIndex,
    foldl,
    get,
    head,
    init,
    iterate,
    last,
    length,
    map,
    maximumBy,
    minimumBy,
    nil,
    null,
    partition,
    product,
    repeat,
    replicate,
    reverse,
    scanl,
    scanr,
    set,
    snoc,
    sortBy,
    span,
    splitAt,
    sum,
    tail,
    take,
    unzip,
    zip,
    zipWith,
  )
import Preloaded
  ( Boolean,
    List (List),
    Number,
    Option,
    Pair,
    both,
    double,
    false,
    just,
    nothing,
    option,
    pair,
    true,
    (?),
  )
import qualified Preloaded as Pre (foldr, uncurry)
import Test.Hspec (Spec, anyException, describe, expectationFailure, it, shouldBe, shouldThrow)
import Text.ParserCombinators.ReadP
  ( ReadP,
    between,
    chainl1,
    char,
    eof,
    look,
    manyTill,
    munch,
    munch1,
    optional,
    readP_to_S,
    satisfy,
    skipSpaces,
    string,
    (+++),
    (<++),
  )

toList :: List a -> [a]
toList xs = Pre.foldr xs (:) []

toBool :: Boolean -> Bool
toBool bool = bool ? True $ False

toMaybe :: Option a -> Maybe a
toMaybe x = option x Nothing Just

toTuple :: Pair a b -> (a, b)
toTuple pair = Pre.uncurry pair (,)

fromList :: [a] -> List a
fromList xs = List $ \c n -> foldr c n xs

fromBool :: Bool -> Boolean
fromBool b | b = true | otherwise = false

fromMaybe :: Maybe a -> Option a
fromMaybe (Just a) = just a
fromMaybe _ = nothing

fromTuple :: (a, b) -> Pair a b
fromTuple = uncurry pair

fromPred :: (a -> Bool) -> (a -> Boolean)
fromPred pred = bool false true . pred

fromCmp :: (a -> a -> Bool) -> (a -> a -> Boolean)
fromCmp cmp = bool false true ... cmp

(...) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(...) = (.) (.) (.)

infixr 8 ...

(#) :: a -> List a -> List a
(#) = L.cons

infixr 5 #

(!) :: List a -> Number -> Option a
(!) = flip L.get

infixl 9 !

spec :: Spec
spec = do
  describe "fixed tests" $ do
    let xs = 3 # 2 # 1 # nil
        inf =
          3
            # 2
            # 1
            # undefined
            # undefined
    describe "instance constructors" $ do
      it "cons, nil" $ do
        toList nil `shouldBe` ([] :: [Number])
        L.sum nil `shouldBe` 0
        L.product nil `shouldBe` 1
        toList (1 # nil) `shouldBe` [1]
        toList (2 # 1 # nil) `shouldBe` [2, 1]
        toList xs `shouldBe` [3, 2, 1]
        L.sum xs `shouldBe` 6
        L.product xs `shouldBe` 6
        toList (L.take 3 inf) `shouldBe` [3, 2, 1]
      it "iterate" $ do
        take 17 (toList $ L.iterate succ 0) `shouldBe` [0 .. 16]
      it "repeat" $ do
        take 17 (toList $ L.repeat 5) `shouldBe` 5 <$ [0 .. 16]
      it "cycle" $ do
        take 17 (toList $ L.cycle xs) `shouldBe` [3, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 3, 2]
        evaluate (L.cycle nil) `shouldThrow` anyException
        toList (L.take 3 $ L.cycle inf) `shouldBe` [3, 2, 1]
      it "replicate" $ do
        toList (L.replicate 17 5) `shouldBe` 5 <$ [0 .. 16]
    describe "helpers" $ do
      it "null" $ do
        toBool (L.null nil) `shouldBe` True
        toBool (L.null $ undefined # nil) `shouldBe` False
        toBool (L.null xs) `shouldBe` False
      it "length" $ do
        L.length nil `shouldBe` 0
        L.length (undefined # nil) `shouldBe` 1
        L.length (undefined # undefined # nil) `shouldBe` 2
        L.length xs `shouldBe` 3
      it "snoc" $ do
        toList (L.snoc (L.snoc (L.snoc nil 1) 2) 3) `shouldBe` [1, 2, 3]
      it "append" $ do
        toList (L.append nil nil) `shouldBe` ([] :: [Number])
        toList (L.append nil xs) `shouldBe` [3, 2, 1]
        toList (L.append xs nil) `shouldBe` [3, 2, 1]
        toList (L.append xs xs) `shouldBe` [3, 2, 1, 3, 2, 1]
        toList (L.append (1 # 2 # 3 # nil) (4 # 5 # 6 # nil)) `shouldBe` [1, 2, 3, 4, 5, 6]
        toList (L.take 6 $ L.append xs inf) `shouldBe` [3, 2, 1, 3, 2, 1]
      it "concat" $ do
        toList (L.concat nil) `shouldBe` ([] :: [Number])
        toList (L.concat $ nil # nil # nil # nil) `shouldBe` ([] :: [Number])
        toList (L.concat $ xs # nil # xs # nil # xs # nil) `shouldBe` [3, 2, 1, 3, 2, 1, 3, 2, 1]
        toList (L.take 3 $ L.concat $ fromList [inf, inf, inf]) `shouldBe` [3, 2, 1]
      it "map" $ do
        toList (L.map undefined nil) `shouldBe` ([] :: [Number])
        L.sum (L.map undefined nil) `shouldBe` 0
        L.product (L.map undefined nil) `shouldBe` 1
        toList (L.map (^ 2) xs) `shouldBe` [9, 4, 1]
        L.sum (L.map (^ 2) xs) `shouldBe` 14
        L.product (L.map (^ 2) xs) `shouldBe` 36
        toList (L.take 3 $ L.map (^ 2) inf) `shouldBe` [9, 4, 1]
      it "filter" $ do
        toList (L.filter undefined nil) `shouldBe` ([] :: [Number])
        L.sum (L.filter undefined nil) `shouldBe` 0
        L.product (L.filter undefined nil) `shouldBe` 1
        toList (L.filter (fromPred odd) xs) `shouldBe` [3, 1]
        L.sum (L.filter (fromPred odd) xs) `shouldBe` 4
        L.product (L.filter (fromPred odd) xs) `shouldBe` 3
        toList (L.filter (fromPred even) xs) `shouldBe` [2]
        L.sum (L.filter (fromPred even) xs) `shouldBe` 2
        L.product (L.filter (fromPred even) xs) `shouldBe` 2
        toList (L.take 1 $ L.filter (fromPred odd) inf) `shouldBe` [3]
      it "take" $ do
        toList (L.take 0 xs) `shouldBe` ([] :: [Number])
        toList (L.take 1 xs) `shouldBe` [3]
        toList (L.take 2 xs) `shouldBe` [3, 2]
        toList (L.take 3 xs) `shouldBe` [3, 2, 1]
        toList (L.take 4 xs) `shouldBe` [3, 2, 1]
        toList (L.take 4 $ 5 # 4 # 3 # 2 # 1 # undefined) `shouldBe` [5, 4, 3, 2]
        toList (L.take 5 $ 5 # 4 # 3 # 2 # 1 # undefined # undefined) `shouldBe` [5, 4, 3, 2, 1]
      it "drop" $ do
        toList (L.drop 0 xs) `shouldBe` [3, 2, 1]
        toList (L.drop 1 xs) `shouldBe` [2, 1]
        toList (L.drop 2 xs) `shouldBe` [1]
        toList (L.drop 3 xs) `shouldBe` []
        toList (L.drop 4 xs) `shouldBe` []
        toList (L.take 2 $ L.drop 1 inf) `shouldBe` [2, 1]
      it "splitAt" $ do
        toTuple (both toList $ L.splitAt 0 xs) `shouldBe` ([], [3, 2, 1])
        toTuple (both toList $ L.splitAt 1 xs) `shouldBe` ([3], [2, 1])
        toTuple (both toList $ L.splitAt 2 xs) `shouldBe` ([3, 2], [1])
        toTuple (both toList $ L.splitAt 3 xs) `shouldBe` ([3, 2, 1], [])
        toTuple (both toList $ L.splitAt 4 xs) `shouldBe` ([3, 2, 1], [])
        toTuple (both (toList . L.take 1) $ L.splitAt 2 inf) `shouldBe` ([3], [1])
      it "get" $ do
        toMaybe (xs ! 0) `shouldBe` Just 3
        toMaybe (xs ! 1) `shouldBe` Just 2
        toMaybe (xs ! 2) `shouldBe` Just 1
        toMaybe (xs ! 4) `shouldBe` Nothing
        toMaybe (inf ! 0) `shouldBe` Just 3
        toMaybe (inf ! 1) `shouldBe` Just 2
        toMaybe (inf ! 2) `shouldBe` Just 1
      it "set" $ do
        toList (L.set 0 4 xs) `shouldBe` [4, 2, 1]
        toList (L.set 1 4 xs) `shouldBe` [3, 4, 1]
        toList (L.set 2 4 xs) `shouldBe` [3, 2, 4]
        toList (L.set 3 4 xs) `shouldBe` [3, 2, 1]
        toList (L.take 3 $ L.set 0 4 inf) `shouldBe` [4, 2, 1]
        toList (L.take 3 $ L.set 1 4 inf) `shouldBe` [3, 4, 1]
        toList (L.take 3 $ L.set 2 4 inf) `shouldBe` [3, 2, 4]
    describe "helpers" $ do
      it "any" $ do
        toBool (L.any (fromPred odd) nil) `shouldBe` False
        toBool (L.any (fromPred even) nil) `shouldBe` False
        toBool (L.any (fromPred odd) $ 2 # 4 # nil) `shouldBe` False
        toBool (L.any (fromPred even) $ 1 # 3 # nil) `shouldBe` False
        toBool (L.any (fromPred odd) xs) `shouldBe` True
        toBool (L.any (fromPred even) xs) `shouldBe` True
        toBool (L.any (fromPred odd) inf) `shouldBe` True
        toBool (L.any (fromPred even) inf) `shouldBe` True
      it "all" $ do
        toBool (L.all (fromPred odd) nil) `shouldBe` True
        toBool (L.all (fromPred even) nil) `shouldBe` True
        toBool (L.all (fromPred odd) $ 1 # 3 # nil) `shouldBe` True
        toBool (L.all (fromPred even) $ 2 # 4 # nil) `shouldBe` True
        toBool (L.all (fromPred odd) xs) `shouldBe` False
        toBool (L.all (fromPred even) xs) `shouldBe` False
        toBool (L.all (fromPred odd) inf) `shouldBe` False
        toBool (L.all (fromPred even) inf) `shouldBe` False
      it "find" $ do
        toMaybe (L.find undefined nil) `shouldBe` (Nothing :: Maybe Number)
        toMaybe (L.find (fromPred odd) $ 1 # nil) `shouldBe` Just 1
        toMaybe (L.find (fromPred even) $ 1 # nil) `shouldBe` Nothing
        toMaybe (L.find (fromPred odd) $ 2 # 1 # nil) `shouldBe` Just 1
        toMaybe (L.find (fromPred even) $ 2 # 1 # nil) `shouldBe` Just 2
        toMaybe (L.find (fromPred odd) xs) `shouldBe` Just 3
        toMaybe (L.find (fromPred even) xs) `shouldBe` Just 2
        toMaybe (L.find (fromPred (== 1)) xs) `shouldBe` Just 1
        toMaybe (L.find (fromPred (== 0)) xs) `shouldBe` Nothing
        toMaybe (L.find (fromPred (== 1)) inf) `shouldBe` Just 1
      it "findIndex" $ do
        toMaybe (L.findIndex undefined nil) `shouldBe` Nothing
        toMaybe (L.findIndex (fromPred odd) $ 1 # nil) `shouldBe` Just 0
        toMaybe (L.findIndex (fromPred even) $ 1 # nil) `shouldBe` Nothing
        toMaybe (L.findIndex (fromPred odd) $ 2 # 1 # nil) `shouldBe` Just 1
        toMaybe (L.findIndex (fromPred even) $ 2 # 1 # nil) `shouldBe` Just 0
        toMaybe (L.findIndex (fromPred odd) xs) `shouldBe` Just 0
        toMaybe (L.findIndex (fromPred even) xs) `shouldBe` Just 1
        toMaybe (L.findIndex (fromPred (== 1)) xs) `shouldBe` Just 2
        toMaybe (L.findIndex (fromPred (== 0)) xs) `shouldBe` Nothing
        toMaybe (L.findIndex (fromPred (== 1)) inf) `shouldBe` Just 2
      it "partition" $ do
        toTuple (both toList $ L.partition (fromPred odd) nil) `shouldBe` ([], [])
        toTuple (both toList $ L.partition (fromPred even) nil) `shouldBe` ([], [])
        toTuple (both toList $ L.partition (fromPred odd) xs) `shouldBe` ([3, 1], [2])
        toTuple (both toList $ L.partition (fromPred even) xs) `shouldBe` ([2], [3, 1])
        toTuple (both (toList . L.take 1) $ L.partition (fromPred odd) $ 4 # inf) `shouldBe` ([3], [4])
      it "span" $ do
        toTuple (both toList $ L.span (fromPred odd) nil) `shouldBe` ([], [])
        toTuple (both toList $ L.span (fromPred even) nil) `shouldBe` ([], [])
        toTuple (both toList $ L.span (fromPred odd) xs) `shouldBe` ([3], [2, 1])
        toTuple (both toList $ L.span (fromPred even) xs) `shouldBe` ([], [3, 2, 1])
        toTuple (both (toList . L.take 1) $ L.span (fromPred odd) inf) `shouldBe` ([3], [2])
      it "minimumBy" $ do
        toMaybe (L.minimumBy undefined nil) `shouldBe` (Nothing :: Maybe Number)
        toMaybe (L.minimumBy (fromCmp (<=)) $ 3 # 2 # 1 # nil) `shouldBe` Just 1
        toMaybe (L.minimumBy (fromCmp (<=)) $ 1 # 2 # 3 # nil) `shouldBe` Just 1
        toMaybe (L.minimumBy (fromCmp (<=)) $ 3 # 1 # 2 # nil) `shouldBe` Just 1
      it "maximumBy" $ do
        toMaybe (L.maximumBy undefined nil) `shouldBe` (Nothing :: Maybe Number)
        toMaybe (L.maximumBy (fromCmp (<=)) $ 3 # 2 # 1 # nil) `shouldBe` Just 3
        toMaybe (L.maximumBy (fromCmp (<=)) $ 1 # 2 # 3 # nil) `shouldBe` Just 3
        toMaybe (L.maximumBy (fromCmp (<=)) $ 3 # 1 # 2 # nil) `shouldBe` Just 3
      it "sortBy" $ do
        toList (L.sortBy undefined nil) `shouldBe` ([] :: [Number])
        toList (L.sortBy (fromCmp (<=)) xs) `shouldBe` [1, 2, 3]
        toList (L.sortBy (fromCmp (<=)) $ 1 # 2 # 3 # nil) `shouldBe` [1, 2, 3]
        toList (L.sortBy (fromCmp (<=)) $ 3 # 1 # 2 # nil) `shouldBe` [1, 2, 3]
    describe "helpers" $ do
      it "foldl" $ do
        L.foldl nil undefined 0 `shouldBe` 0
        L.foldl xs (+) 0 `shouldBe` 6
        L.foldl xs (flip (:)) [] `shouldBe` [1, 2, 3]
      it "scanl" $ do
        toList (L.scanl xs (+) 0) `shouldBe` [0, 3, 5, 6]
      it "scanr" $ do
        toList (L.scanr xs (+) 0) `shouldBe` [6, 3, 1, 0]
      it "reverse" $ do
        toList (L.reverse nil) `shouldBe` ([] :: [Number])
        L.sum (L.reverse nil) `shouldBe` 0
        L.product (L.reverse nil) `shouldBe` 1
        toList (L.reverse xs) `shouldBe` [1, 2, 3]
        L.sum (L.reverse xs) `shouldBe` 6
        L.product (L.reverse xs) `shouldBe` 6
      it "head" $ do
        toMaybe (L.head nil) `shouldBe` (Nothing :: Maybe ())
        toMaybe (L.head $ 1 # nil) `shouldBe` Just 1
        toMaybe (L.head $ 2 # 1 # nil) `shouldBe` Just 2
        toMaybe (L.head xs) `shouldBe` Just 3
        toMaybe (L.head $ 1 # undefined) `shouldBe` Just 1
      it "tail" $ do
        toList <$> toMaybe (L.tail nil) `shouldBe` (Nothing :: Maybe [Number])
        L.sum <$> toMaybe (L.tail nil) `shouldBe` Nothing
        L.product <$> toMaybe (L.tail nil) `shouldBe` Nothing
        toList <$> toMaybe (L.tail $ 1 # nil) `shouldBe` Just []
        toList <$> toMaybe (L.tail $ 2 # 1 # nil) `shouldBe` Just [1]
        toList <$> toMaybe (L.tail xs) `shouldBe` Just [2, 1]
        L.sum <$> toMaybe (L.tail xs) `shouldBe` Just 3
        L.product <$> toMaybe (L.tail xs) `shouldBe` Just 2
        (toList . L.take 2) <$> toMaybe (L.tail inf) `shouldBe` Just [2, 1]
      it "init" $ do
        toList <$> toMaybe (L.init nil) `shouldBe` (Nothing :: Maybe [Number])
        toList <$> toMaybe (L.init $ 1 # nil) `shouldBe` Just []
        toList <$> toMaybe (L.init $ 2 # 1 # nil) `shouldBe` Just [2]
        toList <$> toMaybe (L.init xs) `shouldBe` Just [3, 2]
      it "last" $ do
        toMaybe (L.last nil) `shouldBe` (Nothing :: Maybe Number)
        toMaybe (L.last $ 1 # nil) `shouldBe` Just 1
        toMaybe (L.last $ 2 # 1 # nil) `shouldBe` Just 1
        toMaybe (L.last xs) `shouldBe` Just 1
      it "zip" $ do
        toTuple <$> toList (L.zip nil nil) `shouldBe` ([] :: [(Number, Number)])
        toTuple <$> toList (L.zip nil xs) `shouldBe` ([] :: [(Number, Number)])
        toTuple <$> toList (L.zip xs nil) `shouldBe` ([] :: [(Number, Number)])
        toTuple <$> toList (L.zip xs xs) `shouldBe` [(3, 3), (2, 2), (1, 1)]
        toTuple <$> toList (L.zip xs $ 'a' # 'b' # 'c' # nil) `shouldBe` [(3, 'a'), (2, 'b'), (1, 'c')]
        toTuple <$> toList (L.zip inf $ 'a' # 'b' # nil) `shouldBe` [(3, 'a'), (2, 'b')]
      it "unzip" $ do
        toTuple (double toList toList $ L.unzip nil) `shouldBe` ([] :: [Number], [] :: [Number])
        toTuple (double toList toList $ L.unzip $ pair 3 'a' # pair 2 'b' # pair 1 'c' # nil) `shouldBe` ([3, 2, 1], "abc")
      it "zipWith" $ do
        toTuple <$> toList (L.zipWith pair nil nil) `shouldBe` ([] :: [(Number, Number)])
        toTuple <$> toList (L.zipWith pair nil xs) `shouldBe` ([] :: [(Number, Number)])
        toTuple <$> toList (L.zipWith pair xs nil) `shouldBe` ([] :: [(Number, Number)])
        toTuple <$> toList (L.zipWith pair xs xs) `shouldBe` [(3, 3), (2, 2), (1, 1)]
        toList (L.zipWith (+) xs xs) `shouldBe` [6, 4, 2]
        toList (L.zipWith (+) xs inf) `shouldBe` [6, 4, 2]

-- describe "syntax check" $ do
--   it "Lambda Calculus syntax only" $ do
--     source <- lines <$> readFile "/workspace/solution.txt"
--     for_ source $ \line -> do
--       unless (check line) $
--         expectationFailure $
--           "expected your code to be in Lambda Calculus form\noffending line: " ++ show line

check :: String -> Bool
check line = readP_to_S (sp *> legalLine <* eof) line == [((), "")]

legalLine, moduleLine, importLine, newtypeLine, typeSignature, definition, emptyLine, comment :: ReadP ()
legalLine = moduleLine <++ importLine <++ newtypeLine <++ typeSignature +++ definition <++ emptyLine <* optional comment
moduleLine = void $ string "module " <* munch (const True)
importLine = void $ string "import " <* string "Prelude" <++ string "Preloaded" <* munch (const True)
newtypeLine = void $ string "newtype " <* munch (const True)
typeSignature = expectName `chainl1` ((<>) <$ char ',' <* sp) <* string "::" <* munch (const True)
definition = (expectEmpty <++ expectName) `chainl1` pure (<>) <* char '=' <* sp <* expression
emptyLine = pure ()
comment = void $ string "-- " <* munch (const True)

expression, application, abstraction, expectEmpty, expectSign, expectName, expectNumber, expressionEnds, sp :: ReadP ()
expression = application
application =
  void $
    (paren'd expression <++ abstraction <++ expectSign <++ expectName +++ expectNumber) `manyTill` expressionEnds
abstraction = void $ char '\\' <* sp <* (expectEmpty <++ expectName) `chainl1` pure (<>) <* string "->" <* sp <* expression
expectEmpty = void $ char '_' <* sp
expectSign = void $ char '$' <++ char '?' <* sp
expectName = void $ satisfy isLetter <* munch ((||) <$> isLetter <*> isDigit) <* sp
expectNumber = void $ munch1 isDigit <* sp
expressionEnds = do source <- look; guard (null source || head source == ')' || take 2 source == "--")
sp = skipSpaces

paren'd :: ReadP () -> ReadP ()
paren'd = between (char '(' <* sp) (char ')' <* sp)