module TypeTranspilerSpec where

import TypeTranspiler
import Test.Hspec

a =>> b = transpile a `shouldBe` Right b
keep a = a =>> a

infix 2 =>>

gg a = transpile a `shouldBe` Left "Hugh?"

spec :: Spec
spec = do
  describe "simple and easy tests" $ do
    it "should work when nothing should be changed" $ do
      keep "A"
      keep "_"
      gg "A."
      gg "A.123"
    it "should work when there are generic parameters" $ do
      keep "A<A>"
      gg "A<"
      "List<Int>" =>> "List<Integer>"
      gg "A>"
      "Int.Companion" =>> "Integer.Companion"
      gg "<A>"
    it "should work for star projections" $ do
      "A<*>" =>> "A<?>"
      "A<*, *, A>" =>> "A<?,?,A>"
      gg "?"
      gg "*<A>"
    it "should work for variance" $ do
      "A<in A>" =>> "A<? super A>"
      "List<out T>" =>> "List<? extends T>"
      "Array<out CSharp, out Java>" =>> "Array<? extends CSharp,? extends Java>"
      "ArrayList<in out>" =>> "ArrayList<? super out>"
      "ArrayList<out in>" =>> "ArrayList<? extends in>"
      keep "A<in>"
      keep "Array<out>"
    it "should rename" $ do
      "Int" =>> "Integer"
      "List<Int>" =>> "List<Integer>"
    it "should remove spaces" $ do
      "A<A, B>" =>> "A<A,B>"
    it "should work when there are multiple generic parameters" $ do
      keep "A<A<A>>"
      keep "A<A<A<A<A>>>>"
      keep "A<A,B,C,D>"

  describe "complex tests" $ do
    it "should work for function types" $ do
      "(A) -> B" =>> "Function1<A,B>"
      "(A, B) -> C" =>> "Function2<A,B,C>"
      gg "() -> ()"
    it "should work for complex function types" $ do
      "((A) -> B) -> C" =>> "Function1<Function1<A,B>,C>"
      "(A) -> (B) -> C" =>> "Function1<A,Function1<B,C>>"
      "(((A) -> B) -> C) -> D" =>> "Function1<Function1<Function1<A,B>,C>,D>"
      "(A, B) -> C" =>> "Function2<A,B,C>"
      "((A) -> B, (B) -> C) -> (A) -> C" =>> "Function2<Function1<A,B>,Function1<B,C>,Function1<A,C>>"
