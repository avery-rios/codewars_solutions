object Kata {
  def arrayDiff(a: Seq[Int], b: Seq[Int]): Seq[Int] = {
    val s = b.toSet
    a.filterNot(s.contains)
  }
}
