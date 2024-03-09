{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module AssemblerInterpreter (interpret) where

import Control.Applicative
import Control.Monad.ST
import Data.Attoparsec.Text
import Data.Bifunctor
import Data.Char
import Data.Foldable
import Data.Functor (void)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LTB
import qualified Data.Text.Lazy.Builder.Int as LTB
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed.Mutable as UVM

data PiValue = PvReg Text | PvImm Int
  deriving (Show)

data PiMsgVal = PmReg Text | PmImm Text
  deriving (Show)

data PreInst
  = PiMov Text PiValue
  | PiInc Text
  | PiDec Text
  | PiAdd Text PiValue
  | PiSub Text PiValue
  | PiMul Text PiValue
  | PiDiv Text PiValue
  | PiJmp Text
  | PiCmp PiValue PiValue
  | PiJne Text
  | PiJe Text
  | PiJge Text
  | PiJg Text
  | PiJle Text
  | PiJl Text
  | PiCall Text
  | PiRet
  | PiMsg [PiMsgVal]
  | PiEnd
  deriving (Show)

data Labeled = Labeled [Text] PreInst
  deriving (Show)

skipSpace1 :: Parser ()
skipSpace1 = space >> skipSpace

regP :: Parser Text
regP = takeWhile1 isAlpha

labelP :: Parser Text
labelP = takeWhile1 (\c -> c /= ':' && not (isSpace c))

valueP :: Parser PiValue
valueP = (PvReg <$> regP) <|> (PvImm <$> signed decimal)

uInstP :: (a -> PreInst) -> Text -> Parser a -> Parser PreInst
uInstP c n p = string n >> skipSpace1 >> fmap c p

jmpInstP :: (Text -> PreInst) -> Text -> Parser PreInst
jmpInstP c n = uInstP c n labelP

binInstP :: (a -> b -> PreInst) -> Text -> Parser a -> Parser b -> Parser PreInst
binInstP c n pa pb =
  string n
    >> skipSpace1
    >> liftA2 c pa (skipSpace >> char ',' >> skipSpace >> pb)

regValInstP :: (Text -> PiValue -> PreInst) -> Text -> Parser PreInst
regValInstP c n = binInstP c n regP valueP

instP :: Parser PreInst
instP =
  choice
    [ regValInstP PiMov "mov",
      uInstP PiInc "inc" regP,
      uInstP PiDec "dec" regP,
      regValInstP PiAdd "add",
      regValInstP PiSub "sub",
      regValInstP PiMul "mul",
      regValInstP PiDiv "div",
      jmpInstP PiJmp "jmp",
      binInstP PiCmp "cmp" valueP valueP,
      jmpInstP PiJne "jne",
      jmpInstP PiJe "je",
      jmpInstP PiJge "jge",
      jmpInstP PiJg "jg",
      jmpInstP PiJle "jle",
      jmpInstP PiJl "jl",
      jmpInstP PiCall "call",
      PiRet <$ (string "ret" >> space),
      PiMsg
        <$> ( string "msg"
                >> skipSpace1
                >> sepBy1'
                  ( ( fmap PmReg regP
                        <|> fmap PmImm (char '\'' >> takeTill (== '\'') <* char '\'')
                    )
                      <* skipSpace
                  )
                  (char ',' >> skipSpace)
            ),
      PiEnd <$ (string "end" >> space)
    ]

-- | skip spaces and comment
skipSpComm :: Parser ()
skipSpComm =
  skipSpace
    >> void (optional (char ';' >> takeTill (== '\n') >> skipSpace))

labeledP :: Parser Labeled
labeledP =
  fmap (Labeled []) instP <|> do
    l <- labelP <* char ':'
    skipSpComm
    Labeled ls i <- labeledP
    pure (Labeled (l : ls) i)

progP :: Parser [Labeled]
progP = many (skipSpComm >> labeledP) <* skipSpComm

parsePre :: Text -> Either String [Labeled]
parsePre = parseOnly (progP <* endOfInput)

newtype Reg = Reg Int
  deriving (Show)

newtype IAddr = IAddr Int
  deriving (Show)

data MsgVal = ImReg Reg | ImImm Text
  deriving (Show)

data Instr
  = IMov Reg Reg
  | IMovI Reg Int
  | IAdd Reg Reg
  | IAddI Reg Int
  | ISub Reg Reg
  | IMul Reg Reg
  | IMulI Reg Int
  | IDiv Reg Reg
  | IDivI Reg Int
  | IJmp IAddr
  | ICmpRR Reg Reg
  | ICmpRI Reg Int
  | ICmpIR Int Reg
  | ICmpII Ordering
  | IJNe IAddr
  | IJEq IAddr
  | IJGe IAddr
  | IJGt IAddr
  | IJLe IAddr
  | IJLt IAddr
  | ICall IAddr
  | IRet
  | IMsg (V.Vector MsgVal)
  | IEnd

labelAddr :: [Labeled] -> HM.HashMap Text IAddr
labelAddr lbl =
  foldl'
    ( \mp (i, Labeled ls _) ->
        foldl' (\m l -> HM.insert l (IAddr i) m) mp ls
    )
    HM.empty
    (zip [0 ..] lbl)

type RegMap = HM.HashMap Text Reg

newtype ConvM a = ConvM {unConvM :: RegMap -> Maybe (a, RegMap)}

instance Functor ConvM where
  fmap f (ConvM g) = ConvM (\mp -> fmap (first f) (g mp))

instance Applicative ConvM where
  pure v = ConvM (\mp -> Just (v, mp))
  liftA2 f (ConvM g1) (ConvM g2) =
    ConvM
      ( \mp ->
          do
            (v1, m1) <- g1 mp
            (v2, m2) <- g2 m1
            pure (f v1 v2, m2)
      )

instance Monad ConvM where
  ConvM l >>= f =
    ConvM
      ( \mp -> do
          (v1, m1) <- l mp
          unConvM (f v1) m1
      )

getReg :: Text -> ConvM Reg
getReg t =
  ConvM
    ( \rm ->
        case HM.lookup t rm of
          Just r -> Just (r, rm)
          Nothing ->
            let r = Reg (HM.size rm)
             in Just (r, HM.insert t r rm)
    )

getAddr :: Text -> HM.HashMap Text IAddr -> ConvM IAddr
getAddr t m =
  ConvM
    ( \mp ->
        case HM.lookup t m of
          Just a -> Just (a, mp)
          Nothing -> Nothing
    )

convRegVal :: (Reg -> Reg -> Instr) -> (Reg -> Int -> Instr) -> Text -> PiValue -> ConvM Instr
convRegVal cr _ r1 (PvReg r2) = liftA2 cr (getReg r1) (getReg r2)
convRegVal _ ci r1 (PvImm i) = fmap (\r -> ci r i) (getReg r1)

toInstr :: [Labeled] -> Maybe (V.Vector Instr, Int)
toInstr ls =
  let lm = labelAddr ls
      mp =
        traverse
          ( \(Labeled _ op) -> case op of
              PiMov r1 v -> convRegVal IMov IMovI r1 v
              PiInc r1 -> fmap (\r -> IAddI r 1) (getReg r1)
              PiDec r1 -> fmap (\r -> IAddI r (-1)) (getReg r1)
              PiAdd r1 v -> convRegVal IAdd IAddI r1 v
              PiSub r1 v -> convRegVal ISub (\r i -> IAddI r (-i)) r1 v
              PiMul r1 v -> convRegVal IMul IMulI r1 v
              PiDiv _ (PvImm 0) -> ConvM (\_ -> Nothing)
              PiDiv r1 v -> convRegVal IDiv IDivI r1 v
              PiJmp l -> IJmp <$> getAddr l lm
              PiCmp (PvReg r) v2 -> convRegVal ICmpRR ICmpRI r v2
              PiCmp (PvImm i) (PvReg r) -> ICmpIR i <$> getReg r
              PiCmp (PvImm i) (PvImm i2) -> pure (ICmpII (compare i i2))
              PiJne l -> IJNe <$> getAddr l lm
              PiJe l -> IJEq <$> getAddr l lm
              PiJge l -> IJGe <$> getAddr l lm
              PiJg l -> IJGt <$> getAddr l lm
              PiJle l -> IJLe <$> getAddr l lm
              PiJl l -> IJLt <$> getAddr l lm
              PiCall l -> ICall <$> getAddr l lm
              PiRet -> pure IRet
              PiMsg m ->
                IMsg . V.fromList
                  <$> traverse
                    ( \case
                        PmImm t -> pure (ImImm t)
                        PmReg r -> ImReg <$> getReg r
                    )
                    m
              PiEnd -> pure IEnd
          )
          ls
   in fmap (\(i, mr) -> (V.fromList i, HM.size mr)) (unConvM mp HM.empty)

type RegField s = UVM.MVector s Int

regRegOp :: (Int -> Int -> Int) -> Reg -> Reg -> RegField s -> ST s ()
regRegOp f (Reg r1) (Reg r2) regs = do
  v2 <- UVM.unsafeRead regs r2
  UVM.unsafeModify regs (\v1 -> f v1 v2) r1
{-# INLINE regRegOp #-}

data State = State
  { stack :: [IAddr],
    output :: LTB.Builder,
    cmpState :: Ordering
  }

interp ::
  V.Vector Instr ->
  Int ->
  RegField s ->
  State ->
  ST s (Maybe LT.Text)
interp prog pc regs state =
  case (V.!?) prog pc of
    Just inst -> case inst of
      IMov (Reg r1) (Reg r2) -> do
        UVM.unsafeRead regs r2 >>= UVM.unsafeWrite regs r1
        interp prog (pc + 1) regs state
      IMovI (Reg r) i ->
        UVM.unsafeWrite regs r i
          >> interp prog (pc + 1) regs state
      IAdd r1 r2 ->
        regRegOp (+) r1 r2 regs
          >> interp prog (pc + 1) regs state
      IAddI (Reg r) i ->
        UVM.unsafeModify regs (+ i) r
          >> interp prog (pc + 1) regs state
      ISub r1 r2 ->
        regRegOp (-) r1 r2 regs
          >> interp prog (pc + 1) regs state
      IMul r1 r2 ->
        regRegOp (*) r1 r2 regs
          >> interp prog (pc + 1) regs state
      IMulI (Reg r) i ->
        UVM.unsafeModify regs (* i) r
          >> interp prog (pc + 1) regs state
      IDiv (Reg r) (Reg i) -> do
        UVM.unsafeRead regs i >>= \case
          0 -> pure Nothing
          v2 ->
            UVM.unsafeModify regs (`div` v2) r
              >> interp prog (pc + 1) regs state
      IDivI (Reg r) i ->
        UVM.unsafeModify regs (`div` i) r
          >> interp prog (pc + 1) regs state
      IJmp (IAddr a) -> interp prog a regs state
      ICmpRR (Reg r1) (Reg r2) -> do
        v1 <- UVM.unsafeRead regs r1
        v2 <- UVM.unsafeRead regs r2
        interp prog (pc + 1) regs state {cmpState = compare v1 v2}
      ICmpRI (Reg r1) i -> do
        v1 <- UVM.unsafeRead regs r1
        interp prog (pc + 1) regs state {cmpState = compare v1 i}
      ICmpIR i (Reg r2) -> do
        v2 <- UVM.unsafeRead regs r2
        interp prog (pc + 1) regs state {cmpState = compare i v2}
      ICmpII s ->
        interp prog (pc + 1) regs state {cmpState = s}
      IJNe (IAddr i) ->
        interp prog (if cmpState state /= EQ then i else pc + 1) regs state
      IJEq (IAddr i) ->
        interp prog (if cmpState state == EQ then i else pc + 1) regs state
      IJGe (IAddr i) ->
        interp prog (if cmpState state /= LT then i else pc + 1) regs state
      IJGt (IAddr i) ->
        interp prog (if cmpState state == GT then i else pc + 1) regs state
      IJLe (IAddr i) ->
        interp prog (if cmpState state /= GT then i else pc + 1) regs state
      IJLt (IAddr i) ->
        interp prog (if cmpState state == LT then i else pc + 1) regs state
      ICall (IAddr i) ->
        interp prog i regs state {stack = IAddr (pc + 1) : stack state}
      IRet ->
        case stack state of
          [] -> pure Nothing
          IAddr h : t -> interp prog h regs state {stack = t}
      IMsg ms -> do
        o <-
          V.foldM'
            ( \a m -> case m of
                ImImm t -> pure (a <> LTB.fromText t)
                ImReg (Reg r) -> do
                  v <- UVM.unsafeRead regs r
                  pure (a <> LTB.decimal v)
            )
            (output state)
            ms
        interp prog (pc + 1) regs state {output = o}
      IEnd -> pure (Just (LTB.toLazyText (output state)))
    Nothing -> pure Nothing

interpret :: String -> Maybe String
interpret s =
  either (const Nothing) Just (parsePre (T.pack s))
    >>= toInstr
    >>= \(i, r) ->
      LT.unpack
        <$> runST
          ( do
              regs <- UVM.new r
              interp i 0 regs State {stack = [], output = mempty, cmpState = EQ}
          )
