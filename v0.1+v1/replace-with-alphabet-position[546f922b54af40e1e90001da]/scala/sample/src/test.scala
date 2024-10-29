import org.scalatest._
import flatspec._
import matchers.should._

class KataTest extends AnyFlatSpec with Matchers {
  "alphabetPosition(\"The sunset sets at twelve o' clock.\")" should "return \"20 8 5 19 21 14 19 5 20 19 5 20 19 1 20 20 23 5 12 22 5 15 3 12 15 3 11\"" in {
    Kata.alphabetPosition("The sunset sets at twelve o' clock.")  shouldBe "20 8 5 19 21 14 19 5 20 19 5 20 19 1 20 20 23 5 12 22 5 15 3 12 15 3 11"
  }
  "alphabetPosition(\"The narwhal bacons at midnight.\")" should "return \"20 8 5 14 1 18 23 8 1 12 2 1 3 15 14 19 1 20 13 9 4 14 9 7 8 20\"" in {
    Kata.alphabetPosition("The narwhal bacons at midnight.")  shouldBe "20 8 5 14 1 18 23 8 1 12 2 1 3 15 14 19 1 20 13 9 4 14 9 7 8 20"
  }
}