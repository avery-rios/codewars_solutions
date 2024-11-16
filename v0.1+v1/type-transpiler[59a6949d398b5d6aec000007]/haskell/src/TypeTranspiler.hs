{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module TypeTranspiler (transpile) where

import Data.Attoparsec.Text
import Data.Char (isAlpha, isAlphaNum)
import Data.Foldable (Foldable (foldMap', foldl'))
import Data.Functor (void)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LTB
import qualified Data.Text.Lazy.Builder.Int as LTB

newtype Name = Name Text
  deriving (Show)

data TypeParam
  = TpStar
  | TpIn Type
  | TpOut Type
  | TpPlain Type
  deriving (Show)

data UserType = UserType Name (Maybe [TypeParam]) (Maybe UserType)
  deriving (Show)

data Type
  = TFunction [Type] Type
  | TUser UserType
  deriving (Show)

nameP :: Parser Name
nameP =
  peekChar' >>= \c ->
    if c /= '_' && not (isAlpha c)
      then fail "Invalid name"
      else Name <$> takeWhile1 (\ch -> isAlphaNum ch || ch == '_')

nameR :: Name -> LTB.Builder
nameR (Name n) = LTB.fromText n

typeParamP :: Parser TypeParam
typeParamP =
  choice
    [ TpStar <$ string "*",
      string "in " >> skipSpace >> TpIn <$> typeP,
      string "out " >> skipSpace >> TpOut <$> typeP,
      TpPlain <$> typeP
    ]

typeParamR :: TypeParam -> LTB.Builder
typeParamR TpStar = "?"
typeParamR (TpIn t) = "? super " <> typeR t
typeParamR (TpOut t) = "? extends " <> typeR t
typeParamR (TpPlain t) = typeR t

commaR :: (a -> LTB.Builder) -> [a] -> LTB.Builder
commaR _ [] = mempty
commaR f [x] = f x
commaR f (x : xs) = foldl' (\acc i -> acc <> "," <> f i) (f x) xs

userTypeP :: Parser UserType
userTypeP = do
  n <- nameP
  skipSpace
  tp <-
    peekChar >>= \case
      Just '<' -> do
        char '<' >> skipSpace
        r <- sepBy1 (typeParamP <* skipSpace) (char ',' <* skipSpace)
        skipSpace
        void (char '>')
        pure (Just r)
      _ -> pure Nothing
  skipSpace
  ut <-
    peekChar >>= \case
      Just '.' -> char '.' >> skipSpace >> Just <$> userTypeP
      _ -> pure Nothing
  pure (UserType n tp ut)

userTypeR :: UserType -> LTB.Builder
userTypeR (UserType n params u) =
  nameR n
    <> ( case params of
           Just ps -> "<" <> commaR typeParamR ps <> ">"
           Nothing -> mempty
       )
    <> ( case u of
           Just ut -> "." <> userTypeR ut
           Nothing -> mempty
       )

typeP :: Parser Type
typeP = do
  peekChar' >>= \case
    '(' -> do
      char '(' >> skipSpace
      params <- sepBy (typeP <* skipSpace) (char ',' <* skipSpace)
      skipSpace >> char ')' >> skipSpace
      string "->" >> skipSpace
      TFunction params <$> typeP
    _ -> TUser <$> userTypeP

typeR :: Type -> LTB.Builder
typeR (TFunction params ret) =
  "Function"
    <> LTB.decimal (length params)
    <> "<"
    <> foldMap' (\p -> typeR p <> ",") params
    <> typeR ret
    <> ">"
typeR (TUser u) = userTypeR u

renameTypeParam :: TypeParam -> TypeParam
renameTypeParam TpStar = TpStar
renameTypeParam (TpIn t) = TpIn (renameType t)
renameTypeParam (TpOut t) = TpOut (renameType t)
renameTypeParam (TpPlain t) = TpPlain (renameType t)

renameUserType :: UserType -> UserType
renameUserType (UserType (Name "Int") Nothing c) =
  UserType (Name "Integer") Nothing (renameUserType <$> c)
renameUserType (UserType (Name "Unit") Nothing c) =
  UserType (Name "Void") Nothing (renameUserType <$> c)
renameUserType
  ( UserType
      (Name "kotlin")
      Nothing
      (Just (UserType (Name "Int") Nothing c))
    ) =
    UserType
      (Name "java")
      Nothing
      ( Just
          ( UserType
              (Name "lang")
              Nothing
              (Just (UserType (Name "Integer") Nothing (renameUserType <$> c)))
          )
      )
renameUserType (UserType n param sub) =
  UserType n (fmap (fmap renameTypeParam) param) (fmap renameUserType sub)

renameType :: Type -> Type
renameType (TFunction params ret) = TFunction (renameType <$> params) (renameType ret)
renameType (TUser u) = TUser (renameUserType u)

transpile :: String -> Either String String
transpile input =
  case parseOnly (skipSpace >> typeP <* skipSpace <* endOfInput) (T.pack input) of
    Right r -> Right (LT.unpack (LTB.toLazyText (typeR (renameType r))))
    Left _ -> Left "Hugh?"
