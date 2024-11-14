import org.scalatest._, prop._

class DominoTiling2xNBoardSpec extends FunSuite with TableDrivenPropertyChecks with Matchers {

  import DominoTiling2xNBoard.twoByN

  val fixedTests = Table[Int, Int, Int](
    ("n", "k", "expected result"),
    (1, 1, 1), (3, 1, 0),
    (1, 2, 2), (4, 2, 4), (7, 2, 2),
    (1, 3, 3), (2, 3, 12), (5, 3, 168),
    (10, 5, 7802599), (20, 10, 4137177),
  )

  test("Fixed tests") { forAll(fixedTests) { twoByN(_, _) shouldBe _ } }
}