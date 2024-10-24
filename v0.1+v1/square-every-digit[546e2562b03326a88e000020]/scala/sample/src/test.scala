import org.scalatest._
import flatspec._
import matchers.should._

class KataTest extends AnyFlatSpec with Matchers {
  "squareDigits(9119)" should "return 811181" in {
    squareDigits(9119) shouldBe 811181
  }
    "squareDigits(0)" should "return 0" in {
    squareDigits(0) shouldBe 0
  }
}