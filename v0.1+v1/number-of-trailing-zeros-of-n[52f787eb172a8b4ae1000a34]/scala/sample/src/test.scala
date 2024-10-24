class ZerosSpec extends org.scalatest.flatspec.AnyFlatSpec {
  private def doTest(n: Int, expected: Int): Unit = 
    assert(zeros(n) == expected, s"for zeros($n)")
  
  "zeros" should "pass basic tests" in {
    val testCases = List( //n, expected
      (0, 0),
      (6, 1),
      (14, 2)
    )
    
    testCases foreach doTest
  }
}