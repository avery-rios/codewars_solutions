class NextSmallerSpec extends org.scalatest.flatspec.AnyFlatSpec {
  "nextSmaller" should "pass basic tests" in {
    val testCases = Seq(
      (907L, Some(790L)),
      (531L, Some(513L)),
      (135L, None),
      (2071L, Some(2017L)),
      (414L, Some(144L)),
      (123456798L, Some(123456789L)),
      (123456789L, None),
      (1234567908L, Some(1234567890L)),
      (513L, Some(351L)),
      (351L, Some(315L)),
      (315L, Some(153L)),
      (153L, Some(135L)),
      (135L, None),
      (100L, None),
      (2071L, Some(2017L)),
      (1207L, Some(1072L)),
      (414L, Some(144L)),
      (123456789L, None),
      (29009L, Some(20990L)),
      (1234567908L, Some(1234567890L)),
      (9999999999L, None),
      (59884848483559L, Some(59884848459853L)),
      (1023456789L, None),
      (51226262651257L, Some(51226262627551L)),
      (202233445566L, None),
      (506789L, None)
    )
    
    testCases.foreach {
      (n, expected) => 
        assertResult(expected, s"\nInput\n n = $n")(nextSmaller(n))
    }
  }
}