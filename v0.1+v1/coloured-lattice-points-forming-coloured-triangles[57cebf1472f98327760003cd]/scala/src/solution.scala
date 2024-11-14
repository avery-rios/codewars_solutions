private type Point = (Int, Int, String)

private def isAligned(a: Point, b: Point, c: Point): Boolean =
  b(1) * c(0) + a(1) * b(0) + a(0) * c(1) ==
    b(0) * c(1) + a(1) * c(0) + a(0) * b(1)

private def countTriangles(points: Array[Point]): Int =
  var r = 0
  for
    i <- 0 until points.length
    j <- (i + 1) until points.length
    k <- (j + 1) until points.length
    if !isAligned(points(i), points(j), points(k))
  do r += 1
  r

def countColouredTriangles(
    points: Seq[(Int, Int, String)]
): (Int, Int, Int, Option[(Seq[String], Int)]) =
  val counts = points
    .groupBy(_._3)
    .map({ (c, ps) => (c, countTriangles(ps.toArray)) })
    .toArray
  (
    points.length,
    counts.length,
    counts.map(_._2).sum,
    counts
      .filter(_._2 != 0)
      .maxByOption(_._2)
      .map({ mx =>
        (counts.filter(_._2 == mx._2).map(_._1).sorted.toSeq, mx._2)
      })
  )
