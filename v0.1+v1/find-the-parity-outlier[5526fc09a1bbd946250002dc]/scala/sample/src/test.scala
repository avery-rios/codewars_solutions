import org.scalatest._
import flatspec._

class ParitySpec extends AnyFlatSpec {
  it should "pass basic tests" in {
    val tests = List(
      (List(2, 4, 6, 8, 10, 3), 3),
      (List(2, 4, 0, 100, 4, 11, 2602, 36), 11),
      (List(160, 3, 1719, 19, 11, 13, -21), 160)
    )

    tests.foreach {
      case (integers, expected) => assertResult(expected, s"\nInput:\n  integers = $integers") {Parity.findOutlier(integers)}
    }
  }
}