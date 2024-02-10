module AlphabeticAnagramsSpec (spec) where

import AlphabeticAnagrams
import Test.Hspec

main = hspec spec
spec = do
  describe "lexiPos" $ do
    it "testing 'A'" $ shouldBe (lexiPos "A") 1    
    it "testing 'ABAB'" $ shouldBe (lexiPos "ABAB") 2   
    it "testing 'AAAB'" $ shouldBe (lexiPos "AAAB") 1   
    it "testing 'BAAA'" $ shouldBe (lexiPos "BAAA") 4
    it "testing 'QUESTION'" $ shouldBe (lexiPos "QUESTION") 24572
    it "testing 'BOOKKEEPER'" $ shouldBe (lexiPos "BOOKKEEPER") 10743
    it "testing 'IMMUNOELECTROPHORETICALLY'" $ shouldBe (lexiPos "IMMUNOELECTROPHORETICALLY") 718393983731145698173
    
    