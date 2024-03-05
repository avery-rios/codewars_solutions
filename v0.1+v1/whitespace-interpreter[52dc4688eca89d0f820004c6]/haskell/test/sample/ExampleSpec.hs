module ExampleSpec (spec) where

import Test.Hspec
import Text.Printf (printf)
import Solution (whitespace)  
import Data.Either
  
spec :: Spec
spec = do
    describe "Empty Prog" $ do
        testWhitespace "\n\n\n" "" ""
    describe "Testing push, output of numbers 0 through 3" $ do
        testWhitespace "    \n\t\n \t\n\n\n" "" "0"
        testWhitespace "   \t\n\t\n \t\n\n\n" "" "1"
        testWhitespace "   \t \n\t\n \t\n\n\n" "" "2"
        testWhitespace "   \t\t\n\t\n \t\n\n\n" "" "3"
    describe "Testing ouput of numbers -1 through -3" $ do
        testWhitespace "  \t\t\n\t\n \t\n\n\n" "" "-1"
        testWhitespace "  \t\t \n\t\n \t\n\n\n" "" "-2"
        testWhitespace "  \t\t\t\n\t\n \t\n\n\n" "" "-3"

    describe "Testing simple flow control edge case" $ do
        testWhitespaceError "" ""
    
    describe "Testing output of letters A through C" $ do
        testWhitespace "   \t     \t\n\t\n  \n\n\n" "" "A"
        testWhitespace "   \t    \t \n\t\n  \n\n\n" "" "B"
        testWhitespace "   \t    \t\t\n\t\n  \n\n\n" "" "C"
    describe "Testing output of letters A through C with comments" $ do
        testWhitespace "blahhhh   \targgggghhh     \t\n\t\n  \n\n\n" "" "A"
        testWhitespace " I heart \t  cats  \t \n\t\n  \n\n\n" "" "B"
        testWhitespace "   \t  welcome  \t\t\n\t\n to the\nnew\nworld\n" "" "C"

-- Tests can be written using Hspec http://hspec.github.io/
-- Add your own tests if needed.

-- Utilities for tests
toReadable :: String -> String
toReadable [] = [] 
toReadable (' ':xs) = 's': toReadable xs
toReadable ('\n':xs) = 'n': toReadable xs
toReadable ('\t':xs) = 't': toReadable xs
toReadable (_:xs) = toReadable xs

testWhitespace :: String -> String -> String -> Spec
testWhitespace code inp exp = 
    it (printf "Running with code %s and input = %s" (toReadable code) inp) $
        whitespace code inp `shouldBe` Right exp

testWhitespaceError code inp = 
    it (printf "Running with code %s and input = %s should give error " (toReadable code) inp) $
        whitespace code inp `shouldSatisfy` isLeft
