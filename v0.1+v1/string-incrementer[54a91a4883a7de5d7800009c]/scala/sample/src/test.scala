import org.scalatest._
import flatspec._

class IncrementStringSpec extends AnyFlatSpec {
  "incrementString" should "pass basic tests" in {
    val testCases = List[(String, String)]( //s, expected
      ("foo", "foo1"),
      ("foobar001", "foobar002"),
      ("foobar1", "foobar2"),
      ("foobar00", "foobar01"),
      ("foobar99", "foobar100"),
      ("", "1"),
      ("foobar000", "foobar001"),
      ("foobar999", "foobar1000"),
      ("foobar00999", "foobar01000"),
      ("fo99obar99", "fo99obar100"),
      ("foobar001", "foobar002"),
      ("f00bar", "f00bar1"),
      ("1", "2"),
      ("009", "010")
    )
    
    testCases.foreach {
      case (s, expected) => assertResult(expected, s"\nInput\n  s = \"$s\"") {incrementString(s)}
    }
  }
}