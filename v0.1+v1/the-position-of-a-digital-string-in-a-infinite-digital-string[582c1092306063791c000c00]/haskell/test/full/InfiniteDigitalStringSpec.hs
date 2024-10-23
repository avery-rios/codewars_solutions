module InfiniteDigitalStringSpec where

import Data.List (findIndex, isPrefixOf, tails)
import Data.Maybe (catMaybes, fromJust, isJust)
import qualified InfiniteDigitalString as User
import Test.Hspec
import Test.QuickCheck

numIndex :: Integer -> Integer
numIndex n
  | n < 10 = n - 1
  | otherwise = go 0 1
  where
    go c i
      | n < 10 ^ (i + 1) = c + i * 9 * 10 ^ (i - 1) + (i + 1) * (n - 10 ^ i)
      | otherwise = go (c + i * 9 * 10 ^ (i - 1)) (i + 1)

indexOf :: String -> String -> Maybe Int
indexOf str pat = findIndex (isPrefixOf pat) (tails str)

check :: String -> String -> Maybe Integer
check str c =
  let ds = take (length str * 2) $ concat $ map show [fromIntegral $ read c ..]
      idx = indexOf ds str
   in if isJust idx then Just (numIndex (read c) + (fromIntegral $ fromJust idx)) else Nothing

compose :: String -> Int -> Int -> [Maybe Integer]
compose str l i =
  let sdt = take (l - i) str
      end = take i $ drop (l - i) str
      lst = if (end == "" || end == "0") then [end ++ sdt] else [end ++ sdt, (show $ (read end) - 1) ++ sdt]
   in map (check str) $ filter (\s -> head s /= '0') lst

construct :: String -> Int -> [Integer]
construct str l = catMaybes $ concat $ map (compose str l) [0 .. l - 1]

findPosition :: String -> Integer
findPosition str
  | all (== '0') str = numIndex (read ('1' : str)) + 1
  | otherwise = minimum $ head $ dropWhile (\l -> (length l) == 0) $ map (construct str) [1 .. length str]

spec :: Spec
spec = do
  describe "Example test" $ do
    it "should pass fixed tests" $ do
      User.findPosition "456" `shouldBe` 3
      User.findPosition "454" `shouldBe` 79
      User.findPosition "455" `shouldBe` 98
      User.findPosition "910" `shouldBe` 8
      User.findPosition "9100" `shouldBe` 188
      User.findPosition "99100" `shouldBe` 187
      User.findPosition "00101" `shouldBe` 190
      User.findPosition "001" `shouldBe` 190
      User.findPosition "00" `shouldBe` 190
      User.findPosition "123456789" `shouldBe` 0
      User.findPosition "1234567891" `shouldBe` 0
      User.findPosition "123456798" `shouldBe` 1000000071
      User.findPosition "10" `shouldBe` 9
      User.findPosition "53635" `shouldBe` 13034
      User.findPosition "040" `shouldBe` 1091
      User.findPosition "11" `shouldBe` 11
      User.findPosition "99" `shouldBe` 168
      User.findPosition "667" `shouldBe` 122
      User.findPosition "0404" `shouldBe` 15050
      User.findPosition "949225100" `shouldBe` 382689688
      User.findPosition "58257860625" `shouldBe` 24674951477
      User.findPosition "3999589058124" `shouldBe` 6957586376885
      User.findPosition "555899959741198" `shouldBe` 1686722738828503
      User.findPosition "01" `shouldBe` 10
      User.findPosition "091" `shouldBe` 170
      User.findPosition "0910" `shouldBe` 2927
      User.findPosition "0991" `shouldBe` 2617
      User.findPosition "09910" `shouldBe` 2617
      User.findPosition "09991" `shouldBe` 35286

  describe "400 random tests - basic" $ do
    it "Should pass short (len: 2-9) random tests" $
      withMaxSuccess 400 $
        forAll (choose (2, 9)) $ \l ->
          forAll (vectorOf l $ elements ['0' .. '9']) $ \str -> do
            User.findPosition str `shouldBe` findPosition str

  describe "400 random tests - advanced" $ do
    it "Should pass long (len: 10-15) random tests" $
      withMaxSuccess 400 $
        forAll (choose (10, 15)) $ \l ->
          forAll (vectorOf l $ elements ['0' .. '9']) $ \str -> do
            User.findPosition str `shouldBe` findPosition str