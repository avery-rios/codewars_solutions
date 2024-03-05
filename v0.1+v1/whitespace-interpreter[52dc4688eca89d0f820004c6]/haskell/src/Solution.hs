{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}

module Solution (whitespace) where

import Control.Monad
-- base < 4.17
import Data.Bifunctor
import Data.Char (chr, ord)
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Data.Maybe (mapMaybe)
import Data.Primitive.ByteArray
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LTB
import qualified Data.Text.Lazy.Builder.Int as LTB
import qualified Data.Vector as V
import qualified Data.Vector.Primitive as PV
import Data.Word (Word8)
import Text.Read (readMaybe)

data Token
  = -- | space
    SP
  | Tab
  | LF
  deriving (Show, Eq)

-- | tab -> 1, sp -> 0, in reverse order
newtype Label = L (PV.Vector Word8)
  deriving (Show, Eq, Ord)

instance Hashable Label where
  hashWithSalt s (L (PV.Vector off len (ByteArray ba))) =
    hashByteArrayWithSalt ba off len s

data PreInstr0
  = PiDup
  | PiSwap
  | PiPop
  | PiAdd
  | PiSub
  | PiMul
  | PiDiv
  | PiMod
  | PiStore
  | PiLoad
  | PiPutChar
  | PiPutInt
  | PiGetChar
  | PiGetInt
  | PiRet
  | PiExit
  deriving (Show)

data PreJump
  = PiCall
  | PiJmp
  | PiJmpEqZero
  | PiJmpLtZero
  deriving (Show)

data PreInt
  = PiPush
  | PiCopy
  | PiDrop
  deriving (Show)

data PreInstr
  = PInt PreInt Int
  | PInst0 PreInstr0
  | PJmp PreJump Label
  deriving (Show)

data Labeled = Labeled [Label] PreInstr
  deriving (Show)

unexpEof :: Either String b
unexpEof = Left "Unexpected eof"

type Parser a = [Token] -> Either String (a, [Token])

intP :: Parser Int
intP [] = unexpEof
intP (sig : t) =
  case sig of
    Tab -> first negate <$> f 0 t
    SP -> f 0 t
    LF -> Left "Only terminate in number"
  where
    f _ [] = unexpEof
    f acc (LF : s) = Right (acc, s)
    f acc (SP : s) = f (acc * 2) s
    f acc (Tab : s) = f (acc * 2 + 1) s

labelP :: Parser Label
labelP = f []
  where
    f _ [] = unexpEof
    f acc (LF : s) = Right (L (PV.fromList acc), s)
    f acc (SP : s) = f (0 : acc) s
    f acc (Tab : s) = f (1 : acc) s

invalidInstr :: Either String b
invalidInstr = Left "Invalid instruction"

instrP :: Parser PreInstr
instrP [] = unexpEof
instrP (SP : cs) =
  case cs of
    SP : ct -> first (PInt PiPush) <$> intP ct
    Tab : SP : ct -> first (PInt PiCopy) <$> intP ct
    Tab : LF : ct -> first (PInt PiDrop) <$> intP ct
    LF : SP : ct -> Right (PInst0 PiDup, ct)
    LF : Tab : ct -> Right (PInst0 PiSwap, ct)
    LF : LF : ct -> Right (PInst0 PiPop, ct)
    _ -> invalidInstr
instrP (Tab : SP : cs) =
  case cs of
    SP : SP : ct -> Right (PInst0 PiAdd, ct)
    SP : Tab : ct -> Right (PInst0 PiSub, ct)
    SP : LF : ct -> Right (PInst0 PiMul, ct)
    Tab : SP : ct -> Right (PInst0 PiDiv, ct)
    Tab : Tab : ct -> Right (PInst0 PiMod, ct)
    _ -> invalidInstr
instrP (Tab : Tab : op : ct) =
  case op of
    SP -> Right (PInst0 PiStore, ct)
    Tab -> Right (PInst0 PiLoad, ct)
    _ -> invalidInstr
instrP (Tab : LF : cs) =
  case cs of
    SP : SP : ct -> Right (PInst0 PiPutChar, ct)
    SP : Tab : ct -> Right (PInst0 PiPutInt, ct)
    Tab : SP : ct -> Right (PInst0 PiGetChar, ct)
    Tab : Tab : ct -> Right (PInst0 PiGetInt, ct)
    _ -> invalidInstr
instrP (LF : cs) =
  case cs of
    SP : Tab : ct -> first (PJmp PiCall) <$> labelP ct
    SP : LF : ct -> first (PJmp PiJmp) <$> labelP ct
    Tab : SP : ct -> first (PJmp PiJmpEqZero) <$> labelP ct
    Tab : Tab : ct -> first (PJmp PiJmpLtZero) <$> labelP ct
    Tab : LF : ct -> Right (PInst0 PiRet, ct)
    LF : LF : ct -> Right (PInst0 PiExit, ct)
    _ -> invalidInstr
instrP _ = invalidInstr

labeledP :: Parser Labeled
labeledP (LF : SP : SP : cs) = do
  (l, ct0) <- labelP cs
  (Labeled ls i, ct1) <- labeledP ct0
  pure (Labeled (l : ls) i, ct1)
labeledP cs = first (Labeled []) <$> instrP cs

progP :: [Token] -> Either String [Labeled]
progP = f []
  where
    f acc [] = pure (reverse acc)
    f acc cs = do
      (i0, cs1) <- labeledP cs
      f (i0 : acc) cs1

parsePre :: String -> Either String [Labeled]
parsePre =
  progP
    . mapMaybe
      ( \case
          ' ' -> Just SP
          '\n' -> Just LF
          '\t' -> Just Tab
          _ -> Nothing
      )

newtype IAddr = IA Int
  deriving (Show)

data Instr
  = IPush {-# UNPACK #-} Int
  | ICopy {-# UNPACK #-} Int
  | IDrop {-# UNPACK #-} Int
  | IDup
  | ISwap
  | IPop
  | IAdd
  | ISub
  | IMul
  | IDiv
  | IMod
  | IStore
  | ILoad
  | IPutChar
  | IPutInt
  | IGetChar
  | IGetInt
  | ICall {-# UNPACK #-} IAddr
  | IJump {-# UNPACK #-} IAddr
  | IJmpEqZero {-# UNPACK #-} IAddr
  | IJmpLtZero {-# UNPACK #-} IAddr
  | IRet
  | IExit
  deriving (Show)

labelToAddr :: HM.HashMap Label IAddr -> PreInstr -> Maybe Instr
labelToAddr _ (PInt op v) =
  pure
    ( case op of
        PiPush -> IPush v
        PiCopy -> ICopy v
        PiDrop -> IDrop v
    )
labelToAddr _ (PInst0 op) =
  pure
    ( case op of
        PiDup -> IDup
        PiSwap -> ISwap
        PiPop -> IPop
        PiAdd -> IAdd
        PiSub -> ISub
        PiMul -> IMul
        PiDiv -> IDiv
        PiMod -> IMod
        PiLoad -> ILoad
        PiStore -> IStore
        PiPutChar -> IPutChar
        PiPutInt -> IPutInt
        PiGetChar -> IGetChar
        PiGetInt -> IGetInt
        PiRet -> IRet
        PiExit -> IExit
    )
labelToAddr lm (PJmp op l) =
  fmap
    ( case op of
        PiCall -> ICall
        PiJmp -> IJump
        PiJmpEqZero -> IJmpEqZero
        PiJmpLtZero -> IJmpLtZero
    )
    (HM.lookup l lm)

toInstr :: [Labeled] -> Either String [Instr]
toInstr ls =
  foldM
    ( \mp (Labeled l _, cnt) ->
        foldM
          ( \m li ->
              if HM.member li m
                then Left "Duplicate label"
                else pure (HM.insert li (IA cnt) m)
          )
          mp
          l
    )
    HM.empty
    (zip ls [0 ..])
    >>= \lm ->
      maybe
        (Left "Unknown label")
        Right
        (traverse (\(Labeled _ i) -> labelToAddr lm i) ls)

type ErrorMsg = String

type Result = Either ErrorMsg String

type Prog = V.Vector Instr

stackAt :: Int -> [Int] -> Maybe Int
stackAt _ [] = Nothing
stackAt 0 (x : _) = Just x
stackAt i (_ : xs) = stackAt (i - 1) xs

emptyStk :: Either String b
emptyStk = Left "Empty stack"

data State = State
  { callStack :: [IAddr],
    heap :: IM.IntMap Int,
    input :: String,
    output :: LTB.Builder
  }

interp :: Prog -> Int -> [Int] -> State -> Either ErrorMsg LTB.Builder
interp is pc stack state =
  case (V.!?) is pc of
    Just op -> case (stack, op) of
      (_, IPush i) -> interp is (pc + 1) (i : stack) state
      (_, ICopy i) -> case stackAt i stack of
        Just v -> interp is (pc + 1) (v : stack) state
        Nothing -> emptyStk
      (x : xs, IDrop i) -> interp is (pc + 1) (x : if i < 0 then [] else L.drop i xs) state
      (x : _, IDup) -> interp is (pc + 1) (x : stack) state
      (x1 : x2 : xs, ISwap) -> interp is (pc + 1) (x2 : x1 : xs) state
      (_ : xs, IPop) -> interp is (pc + 1) xs state
      (a : b : xs, IAdd) -> interp is (pc + 1) (b + a : xs) state
      (a : b : xs, ISub) -> interp is (pc + 1) (b - a : xs) state
      (a : b : xs, IMul) -> interp is (pc + 1) (b * a : xs) state
      (a : b : xs, IDiv)
        | a == 0 -> Left "Divide by zero"
        | otherwise -> interp is (pc + 1) (b `div` a : xs) state
      (a : b : xs, IMod)
        | a == 0 -> Left "Divide by zero"
        | otherwise -> interp is (pc + 1) (b `mod` a : xs) state
      (a : b : xs, IStore) -> interp is (pc + 1) xs state {heap = IM.insert b a (heap state)}
      (a : xs, ILoad) -> case IM.lookup a (heap state) of
        Just v -> interp is (pc + 1) (v : xs) state
        Nothing -> Left "Invalid heap address"
      (a : xs, IPutChar) ->
        interp
          is
          (pc + 1)
          xs
          state {output = output state <> LTB.singleton (chr a)}
      (a : xs, IPutInt) ->
        interp
          is
          (pc + 1)
          xs
          state {output = output state <> LTB.decimal a}
      (b : xs, IGetChar) ->
        case input state of
          [] -> Left "End of input"
          i : ir ->
            interp
              is
              (pc + 1)
              xs
              state {input = ir, heap = IM.insert b (ord i) (heap state)}
      (b : xs, IGetInt) ->
        let (i, ir) = L.break (== '\n') (input state)
         in case readMaybe i of
              Just v ->
                interp
                  is
                  (pc + 1)
                  xs
                  state
                    { input = case ir of
                        [] -> []
                        _ : irt -> irt,
                      heap = IM.insert b v (heap state)
                    }
              Nothing -> Left "Failed to read int"
      (_, ICall (IA p)) ->
        interp
          is
          p
          stack
          state {callStack = IA (pc + 1) : callStack state}
      (_, IJump (IA p)) -> interp is p stack state
      (x : xs, IJmpEqZero (IA p)) -> interp is (if x == 0 then p else pc + 1) xs state
      (x : xs, IJmpLtZero (IA p)) -> interp is (if x < 0 then p else pc + 1) xs state
      (_, IRet) -> case callStack state of
        [] -> Left "No function to return"
        (IA h : t) -> interp is h stack state {callStack = t}
      (_, IExit) -> Right (output state)
      ([], _) -> emptyStk
      ([_], _) -> emptyStk
    Nothing -> Left "Unclean end"

whitespace :: String -> String -> Result
whitespace code i =
  parsePre code >>= toInstr >>= \is ->
    bimap
      (\e -> concat ["code: ", show code, " input: ", show i, " error: ", e])
      (LT.unpack . LTB.toLazyText)
      ( interp
          (V.fromList is)
          0
          []
          State
            { callStack = [],
              heap = IM.empty,
              input = i,
              output = mempty
            }
      )
