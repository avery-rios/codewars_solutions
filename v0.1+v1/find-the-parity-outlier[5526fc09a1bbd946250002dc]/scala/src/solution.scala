object Parity {
  private def isEven(i: Int): Boolean = (i & 1) == 0

  def findOutlier(integers: List[Int]): Int =
    (isEven(integers(0)), isEven(integers(1)), isEven(integers(2))) match
      case (false, false, false) => integers.find(isEven).get
      case (false, false, true)  => integers(2)
      case (false, true, false)  => integers(1)
      case (false, true, true)   => integers(0)
      case (true, false, false)  => integers(0)
      case (true, false, true)   => integers(1)
      case (true, true, false)   => integers(2)
      case (true, true, true)    => integers.find({ v => !isEven(v) }).get
}
