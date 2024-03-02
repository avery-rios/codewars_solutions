{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module SymbolicDifferentiationOfPrefixExpressions (Expr, parseExpr, diff) where

import Control.Applicative
import Data.Attoparsec.Text
import Data.Ratio
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LTB
import qualified Data.Text.Lazy.Builder.Int as LTB
import qualified Data.Text.Lazy.Builder.RealFloat as LTB

type Lit = Ratio Int

litP :: Parser Lit
litP = signed rational

printLit :: Lit -> LTB.Builder
printLit l
  | denominator l == 1 = LTB.decimal (numerator l)
  | otherwise = LTB.realFloat (fromRational (toRational l) :: Double)

data Fun
  = Cos
  | Sin
  | Tan
  | Exp
  | Ln
  deriving (Show)

data BinOp
  = Plus
  | Minus
  | Mul
  | Div
  deriving (Show)

data Expr
  = ELit Lit
  | EVar
  | EBinOp BinOp Expr Expr
  | EFun Fun Expr
  | EPow Expr Int
  deriving (Show)

pattern EPlus :: Expr -> Expr -> Expr
pattern EPlus l r = EBinOp Plus l r

pattern EMinus :: Expr -> Expr -> Expr
pattern EMinus l r = EBinOp Minus l r

pattern EMul :: Expr -> Expr -> Expr
pattern EMul l r = EBinOp Mul l r

pattern EDiv :: Expr -> Expr -> Expr
pattern EDiv l r = EBinOp Div l r

pattern ENeg :: Expr -> Expr
pattern ENeg e = EMul (ELit (-1)) e

space1 :: Parser ()
space1 = space >> skipSpace

exprP :: Parser Expr
exprP =
  choice
    [ EVar <$ char 'x',
      ELit <$> litP,
      char '('
        >> choice
          [ char '^'
              >> space1
              >> liftA2
                EPow
                (exprP <* space1)
                (signed decimal),
            liftA3
              EBinOp
              ( choice
                  [ Plus <$ char '+',
                    Minus <$ char '-',
                    Mul <$ char '*',
                    Div <$ char '/'
                  ]
                  <* space1
              )
              (exprP <* space1)
              exprP,
            liftA2
              EFun
              ( choice
                  [ Cos <$ string "cos",
                    Sin <$ string "sin",
                    Tan <$ string "tan",
                    Exp <$ string "exp",
                    Ln <$ string "ln"
                  ]
                  <* space1
              )
              exprP
          ]
          <* skipSpace
          <* char ')'
    ]

parseExpr :: T.Text -> Either String Expr
parseExpr = parseOnly (exprP <* skipSpace <* endOfInput)

deriv :: Expr -> Expr
deriv (ELit _) = ELit 0
deriv EVar = ELit 1
deriv (EBinOp bop l r) =
  case bop of
    Plus -> EPlus (deriv l) (deriv r)
    Minus -> EMinus (deriv l) (deriv r)
    Mul -> EPlus (deriv l `EMul` r) (l `EMul` deriv r)
    Div ->
      EDiv
        ((deriv l `EMul` r) `EMinus` (l `EMul` deriv r))
        (EPow r 2)
deriv (EFun f e) =
  deriv e
    `EMul` ( case f of
               Cos -> ENeg (EFun Sin e)
               Sin -> EFun Cos e
               Tan -> ELit 1 `EPlus` EPow (EFun Tan e) 2
               Exp -> EFun Exp e
               Ln -> ELit 1 `EDiv` e
           )
deriv (EPow e a) = (ELit (fromIntegral a) `EMul` EPow e (a - 1)) `EMul` deriv e

simplPlus :: Expr -> Expr -> Expr
simplPlus (ELit 0) r = r
simplPlus (ELit l) (ELit r) = ELit (l + r)
simplPlus l (ELit 0) = l
simplPlus l r = EPlus l r

simplMinus :: Expr -> Expr -> Expr
simplMinus l (ELit 0) = l
simplMinus (ELit l) (ELit r) = ELit (l - r)
simplMinus l r = EMinus l r

simplMul :: Expr -> Expr -> Expr
simplMul (ELit 0) _ = ELit 0
simplMul (ELit 1) r = r
simplMul (ELit l) (ELit r) = ELit (l * r)
simplMul _ (ELit 0) = ELit 0
simplMul l (ELit 1) = l
simplMul l r = EMul l r

simplDiv :: Expr -> Expr -> Expr
simplDiv l (ELit 1) = l
simplDiv (ELit 0) _ = ELit 0
simplDiv (ELit l) (ELit r) = ELit (l / r)
simplDiv l r = EDiv l r

simplPow :: Expr -> Int -> Expr
simplPow _ 0 = ELit 1
simplPow e 1 = simpl e
simplPow e a = case simpl e of
  ELit el -> ELit (el ^ a)
  se -> EPow se a

simpl :: Expr -> Expr
simpl e@(ELit _) = e
simpl e@EVar = e
simpl (EBinOp bop l r) =
  let sl = simpl l
      sr = simpl r
   in case bop of
        Plus -> simplPlus sl sr
        Minus -> simplMinus sl sr
        Mul -> simplMul sl sr
        Div -> simplDiv sl sr
simpl (EPow e a) = simplPow e a
simpl (EFun f e) = EFun f (simpl e)

printE :: Expr -> LTB.Builder
printE (ELit l) = printLit l
printE EVar = "x"
printE (EBinOp op l r) =
  mconcat
    [ "(",
      case op of
        Plus -> "+"
        Minus -> "-"
        Mul -> "*"
        Div -> "/",
      " ",
      printE l,
      " ",
      printE r,
      ")"
    ]
printE (EFun f l) =
  mconcat
    [ "(",
      case f of
        Cos -> "cos"
        Sin -> "sin"
        Tan -> "tan"
        Exp -> "exp"
        Ln -> "ln",
      " ",
      printE l,
      ")"
    ]
printE (EPow e a) = mconcat ["(^ ", printE e, " ", LTB.decimal a, ")"]

diff :: String -> String
diff s =
  case parseExpr (T.pack s) of
    Right e -> (LT.unpack . LTB.toLazyText . printE . simpl . deriv) e
    Left err -> error err
