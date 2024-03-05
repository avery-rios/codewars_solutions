{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}

module TinyThreePassCompiler (AST (..), pass1, pass2, pass3, compile) where

import Control.Applicative
import Data.Attoparsec.Text as Atto
import Data.Char (isAlpha)
import Data.Foldable
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T

data AST
  = Imm Int
  | Arg Int
  | Add AST AST
  | Sub AST AST
  | Mul AST AST
  | Div AST AST
  deriving (Eq, Show)

type VarMap = HM.HashMap Text Int

varP :: Parser Text
varP = Atto.takeWhile1 isAlpha

factorP :: VarMap -> Parser AST
factorP mp =
  skipSpace
    >> choice
      [ char '(' >> exprP mp <* char ')',
        Imm <$> signed decimal,
        fmap (Arg . (HM.!) mp) varP
      ]
      <* skipSpace

termP :: VarMap -> Parser AST
termP mp = factorP mp >>= pf
  where
    pf l =
      ( ( ((Mul l <$ char '*') <|> (Div l <$ char '/'))
            <*> factorP mp
        )
          >>= pf
      )
        <|> pure l

exprP :: VarMap -> Parser AST
exprP mp = termP mp >>= pt
  where
    pt l =
      ( (((Add l <$ char '+') <|> (Sub l <$ char '-')) <*> termP mp)
          >>= pt
      )
        <|> pure l

funcP :: Parser AST
funcP = do
  skipSpace
  vs <- char '[' >> skipSpace >> many (varP <* skipSpace) <* char ']'
  let vm = foldl' (\m (v, i) -> HM.insert v i m) HM.empty (zip vs [0 ..])
  exprP vm

compile :: String -> [String]
compile = pass3 . pass2 . pass1

pass1 :: String -> AST
pass1 s = case parseOnly (funcP <* endOfInput) (T.pack s) of
  Right e -> e
  Left e -> error e

simplAdd :: AST -> AST -> AST
simplAdd (Imm 0) r = r
simplAdd l (Imm 0) = l
simplAdd (Imm l) (Imm r) = Imm (l + r)
simplAdd l r = Add l r

simplSub :: AST -> AST -> AST
simplSub l (Imm 0) = l
simplSub (Imm l) (Imm r) = Imm (l - r)
simplSub l r = Sub l r

simplMul :: AST -> AST -> AST
simplMul (Imm 0) _ = Imm 0
simplMul (Imm 1) r = r
simplMul (Imm l) (Imm r) = Imm (l * r)
simplMul _ (Imm 0) = Imm 0
simplMul l (Imm 1) = l
simplMul l r = Mul l r

simplDiv :: AST -> AST -> AST
simplDiv (Imm 0) _ = Imm 0
simplDiv l (Imm 1) = l
simplDiv (Imm l) (Imm r) = Imm (l `div` r)
simplDiv l r = Div l r

pass2 :: AST -> AST
pass2 e@(Imm _) = e
pass2 e@(Arg _) = e
pass2 (Add l r) = simplAdd (pass2 l) (pass2 r)
pass2 (Sub l r) = simplSub (pass2 l) (pass2 r)
pass2 (Mul l r) = simplMul (pass2 l) (pass2 r)
pass2 (Div l r) = simplDiv (pass2 l) (pass2 r)

data Instr
  = IIm Int
  | IAr Int
  | ISw
  | IPu
  | IPo
  | IAd
  | ISu
  | IMu
  | IDi

binOpInstr :: Instr -> AST -> AST -> [Instr] -> [Instr]
binOpInstr op (Imm l) r = toInstr r . (ISw :) . (IIm l :) . (op :)
binOpInstr op (Arg l) r = toInstr r . (ISw :) . (IAr l :) . (op :)
binOpInstr op l r = toInstr l . (IPu :) . toInstr r . (ISw :) . (IPo :) . (op :)

toInstr :: AST -> [Instr] -> [Instr]
toInstr (Imm v) = (IIm v :)
toInstr (Arg a) = (IAr a :)
toInstr (Add l r) = binOpInstr IAd l r
toInstr (Sub l r) = binOpInstr ISu l r
toInstr (Mul l r) = binOpInstr IMu l r
toInstr (Div l r) = binOpInstr IDi l r

pass3 :: AST -> [String]
pass3 a =
  fmap
    ( \case
        IIm i -> "IM " ++ show i
        IAr i -> "AR " ++ show i
        ISw -> "SW"
        IPu -> "PU"
        IPo -> "PO"
        IAd -> "AD"
        ISu -> "SU"
        IMu -> "MU"
        IDi -> "DI"
    )
    (toInstr a [])
