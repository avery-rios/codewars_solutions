{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StrictData #-}

module OperatorParser
  ( OpTree (..),
    Associativity (..),
    op,
    foldTree,
    parseOperators,
    module Text.ParserCombinators.ReadP,
  )
where

import Control.Applicative hiding (many)
import Control.Monad (guard)
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Vector.Generic ((!))
import qualified Data.Vector.Unboxed as UV
import Text.ParserCombinators.ReadP

-- | Type for operator parse results. 'a' is the type of the operator, 'b'
-- | of the terms.
data OpTree a b
  = Op (OpTree a b) a (OpTree a b)
  | Term b
  deriving (Show, Eq, Functor)

-- | Type for specifying the assocativity of operators: left, right, or none.
data Associativity a = L a | R a | NoAssociativity a
  deriving (Show, Eq, Functor)

-- | Transform an OpTree using the given function.
foldTree :: (a -> b -> b -> b) -> OpTree a b -> b
foldTree _ (Term v) = v
foldTree f (Op l v r) = f v (foldTree f l) (foldTree f r)

-- | Return a parser such that: given 'op s a', if s matches, the parser
-- | returns a.
op :: String -> a -> ReadP a
op s a = a <$ string s

data PreOpTree a b
  = POp !a !Int !(PreOpTree a b) !(PreOpTree a b)
  | PTerm !b

toOpTreeF :: UV.Vector Int -> PreOpTree a b -> Maybe (Int, OpTree a b)
toOpTreeF _ (PTerm t) = Just (0, Term t)
toOpTreeF opAssoc (POp o oid l r) =
  let conflict = opAssoc ! oid
   in if conflict == 0
        then
          liftA2
            (\(_, tl) (_, tr) -> (0, Op tl o tr))
            (toOpTreeF opAssoc l)
            (toOpTreeF opAssoc r)
        else do
          (opL, tl) <- toOpTreeF opAssoc l
          guard (opL /= conflict)
          (opR, tr) <- toOpTreeF opAssoc r
          guard (opR /= conflict)
          pure (conflict, Op tl o tr)

toOpTree :: UV.Vector Int -> PreOpTree a b -> Maybe (OpTree a b)
toOpTree opAssoc pt = snd <$> toOpTreeF opAssoc pt

data BindPower = BindPower {bpLeft :: Int, bpRight :: Int}

data OperInfo = OperInfo
  { oId :: Int,
    oBp :: {-# UNPACK #-} BindPower
  }

data OperParser a = OperParser (ReadP a) OperInfo

-- | left binding power position
type LBPPos = UV.Vector Int

-- | operator parser vector, sorted by left bind power
type OperPV a = V.Vector (OperParser a)

parseOp :: OperPV a -> ReadP (a, OperInfo)
parseOp v = case V.uncons v of
  Just (OperParser pOp oi, t) ->
    fmap (\p -> (p, oi)) pOp +++ parseOp t
  Nothing -> pfail

parseL :: LBPPos -> OperPV a -> Int -> PreOpTree a b -> ReadP b -> ReadP (PreOpTree a b)
parseL lpos opv opOff lhs tm =
  ( do
      skipSpaces
      (a, oi) <- parseOp (V.drop opOff opv)
      skipSpaces
      r <- preParse lpos opv (lpos ! bpRight (oBp oi)) tm
      parseL lpos opv opOff (POp a (oId oi) lhs r) tm
  )
    <++ pure lhs

preParse :: LBPPos -> OperPV a -> Int -> ReadP b -> ReadP (PreOpTree a b)
preParse lpos opv opOff tm = do
  l <-
    between
      (char '(')
      (char ')')
      (skipSpaces >> preParse lpos opv 0 tm <* skipSpaces)
      +++ fmap PTerm tm
  parseL lpos opv opOff l tm

data OperAssoc = OaL | OaR | OaNone

data PreOpers a = PreOpers
  { poGroup :: Int,
    poAssoc :: OperAssoc,
    poOpers :: [ReadP a],
    poCount :: Int
  }

preOpers :: [Associativity [ReadP a]] -> [PreOpers a]
preOpers =
  snd
    . L.mapAccumL
      ( \p v ->
          ( p + 1,
            case v of
              L ps -> PreOpers p OaL ps (length ps)
              R ps -> PreOpers p OaR ps (length ps)
              NoAssociativity ps -> PreOpers p OaNone ps (length ps)
          )
      )
      0

operPv :: [PreOpers a] -> OperPV a
operPv =
  V.fromList
    . concat
    . snd
    . L.mapAccumL
      ( \i po ->
          let bp =
                let p = poGroup po
                 in case poAssoc po of
                      OaL -> BindPower {bpLeft = p * 2, bpRight = p * 2 + 1}
                      OaR -> BindPower {bpLeft = p * 2 + 1, bpRight = p * 2}
                      OaNone -> BindPower {bpLeft = p * 2, bpRight = p * 2 + 1}
           in L.mapAccumL
                (\ix p -> (ix + 1, OperParser p OperInfo {oId = ix, oBp = bp}))
                i
                (poOpers po)
      )
      0

leftPowerPos :: [PreOpers a] -> LBPPos
leftPowerPos =
  UV.scanl' (+) 0
    . UV.fromList
    . foldMap
      ( \po ->
          let cnt = poCount po
           in case poAssoc po of
                OaL -> [cnt, 0]
                OaR -> [0, cnt]
                OaNone -> [cnt, 0]
      )

assocInfo :: [PreOpers a] -> UV.Vector Int
assocInfo =
  UV.concat
    . fmap
      ( \po ->
          UV.replicate
            (poCount po)
            ( case poAssoc po of
                OaL -> 0
                OaR -> 0
                OaNone -> poGroup po
            )
      )

-- | Accept two arguments:
-- | (1) A list of type [Associativity [ReadP a]], which contains parsers for
-- | operators (ReadP a). Each item of type Associativity [ReadP a] contains
-- | a group of operator parsers of the same precedence and associativity;
-- | these groups are listed in order of precedence (lowest to highest).
-- | (2) A parser for the terms.
-- | And return a parser for operator expressions that yields a parse tree.
parseOperators :: [Associativity [ReadP a]] -> ReadP b -> ReadP (OpTree a b)
parseOperators ops num =
  let po = preOpers ops
   in preParse (leftPowerPos po) (operPv po) 0 num
        >>= \pt -> maybe pfail pure (toOpTree (assocInfo po) pt)
