import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import Kata._

class CreatePhoneNumberSuite extends AnyFlatSpec with Matchers {
  "createPhoneNumber(Seq(1, 2, 3, 4, 5, 6, 7, 8, 9, 0))" should "return \"(123) 456-7890\"" in {
    createPhoneNumber(Seq(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)) shouldBe "(123) 456-7890"
  }
}