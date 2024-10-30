import org.scalatest._
import flatspec._

class ExampleTest extends AnyFlatSpec {
  "narcissistic(7)" should "return true" in {
    assertResult(true) {Kata.narcissistic(7)}
  }
  "narcissistic(371)" should "return true" in {
    assertResult(true) {Kata.narcissistic(371)}
  }
  "narcissistic(122)" should "return false" in {
    assertResult(false) {Kata.narcissistic(122)}
  }
  "narcissistic(4887)" should "return false" in {
    assertResult(false) {Kata.narcissistic(4887)}
  }
}