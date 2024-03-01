module RegExpParserSpec (spec) where

import Test.Hspec
import RegExpParser (RegExp(..),parseRegExp)
import Data.Foldable (for_)
import Text.Printf (printf)

validate :: [(String,Maybe RegExp)] -> Spec
validate exs = for_ exs $ \ (input,output) -> do
  it (printf "should return %s given %s as input" (show output) (show input)) $ do
    parseRegExp input `shouldBe` output
          
spec :: Spec
spec = do
  describe "Precedence examples" $ do 
    validate [ ( "ab*", Just (Str [Normal 'a', ZeroOrMore (Normal 'b')]) )
             , ( "(ab)*", Just ( ZeroOrMore (Str [Normal 'a', Normal 'b'])) )
             , ( "ab|a", Just (Or (Str [Normal 'a',Normal 'b']) (Normal 'a')) )
             , ( "a(b|a)", Just (Str [Normal 'a',Or (Normal 'b') (Normal 'a')]) )
             , ( "a|b*", Just (Or (Normal 'a') (ZeroOrMore (Normal 'b'))) )
             , ( "(a|b)*", Just (ZeroOrMore (Or (Normal 'a') (Normal 'b'))) )
             ]
  describe "The other examples" $ do 
    validate [ ( "a", Just (Normal 'a') )
             , ( "ab", Just (Str [ Normal 'a', Normal 'b']) )
             , ( "a.*", Just (Str [ Normal 'a', ZeroOrMore Any ]) )
             , ( "(a.*)|(bb)", Just (Or (Str [Normal 'a', ZeroOrMore Any]) (Str [Normal 'b', Normal 'b'])) )
             ]
  describe "Invalid examples" $ do 
    validate [ ( "", Nothing )
             , ( "(", Nothing )
             , ( ")(", Nothing )
             , ( "*", Nothing )
             ]
  describe "Complex examples" $ do 
    validate [ ( "((aa)|ab)*|a", Just (Or (ZeroOrMore (Or (Str [Normal 'a',Normal 'a']) (Str [Normal 'a',Normal 'b']))) (Normal 'a')) )
             , ( "((a.)|.b)*|a", Just (Or (ZeroOrMore (Or (Str [Normal 'a',Any]) (Str [Any,Normal 'b']))) (Normal 'a')) )
             ]