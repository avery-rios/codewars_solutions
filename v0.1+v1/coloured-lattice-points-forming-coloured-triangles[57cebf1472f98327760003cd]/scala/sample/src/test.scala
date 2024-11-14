class CountColouredTrianglesSpec extends org.scalatest.flatspec.AnyFlatSpec {
  "countColouredTriangles" should "pass basic tests" in {
    val testCases = Seq[(Seq[(Int, Int, String)], (Int, Int, Int, Option[(Seq[String], Int)]))](
      (
        Seq(
          (3, -4, "blue"), (-7, -1, "red"), 
          (7, -6, "yellow"), (2, 5, "yellow"), 
          (1, -5, "red"), (-1, 4, "red"), 
          (1, 7, "red"), (-3, 5, "red"), 
          (-3, -5, "blue"), (4, 1, "blue")
        ), 
        (10, 3, 11, Some(Seq("red"), 10))
      ),
      (
        Seq(
          (3, -4, "blue"), (-7, -1, "red"), 
          (7, -6, "yellow"), (2, 5, "yellow"), 
          (1, -5, "red"), (1, 1, "red"), 
          (1, 7, "red"), (1, 4, "red"), 
          (-3, -5, "blue"), (4, 1, "blue")
        ),
        (10, 3, 7, Some(Seq("red"), 6))
      ),
      (
        Seq(
          (1, -2, "red"), 
          (7, -6, "yellow"), (2, 5, "yellow"),
          (1, -5, "red"), (1, 1, "red"), 
          (1, 7, "red"), (1, 4, "red"), 
          (-3, -5, "blue"), (4, 1, "blue")
        ), 
        (9, 3, 0, None)
      )
    )
    
    testCases foreach {
      (points, expected) => 
        assert(countColouredTriangles(points) == expected, s"\npoints = $points")
    }
  }
}