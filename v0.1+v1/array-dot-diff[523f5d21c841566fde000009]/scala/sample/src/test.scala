import org.scalatest.funspec._
import Kata._

class ArrayDiffSuite extends AnyFunSpec {

  val tests = Seq(
    (Seq(1, 2), Seq(1), Seq(2)),
    (Seq(1, 2, 2), Seq(1), Seq(2, 2)),
    (Seq(1, 2, 2), Seq(2), Seq(1)),
    (Seq(1, 2, 2), Seq(), Seq(1, 2, 2)),
    (Seq(), Seq(1, 2), Seq())
  )

  describe("Basic tests:") {
    tests.foreach { case (a, b, expected) =>
      it(s" Difference between $a and $b should be $expected") {
        assert(arrayDiff(a, b) == expected)
      }
    }
  }
}