object DominoTiling2xNBoard {
  private val m = 12345787

  private def sub(l: Long, r: Long): Long =
    if (l >= r) {
      l - r
    } else {
      l + m - r
    }

  private case class State(
      // last is vertical
      val vertical: Long,
      // last is horizontal
      val horizontal: Long,
      val sum: Long
  );
  private object State {
    def apply(k: Long, k2: Long, vertical: Long, horizontal: Long): State =
      State(vertical, horizontal, (vertical * k + horizontal * k2) % m)

  }

  def twoByN(n: Int, k: Int): Int = k match {
    case 0 => 0
    case 1 =>
      if (n == 1) { 1 }
      else { 0 }
    case _ => {
      val kl: Long = k.toLong
      val kl2 = (kl * (kl - 1)) % m

      var current = State(1, 0, kl)
      var next = State(
        kl,
        kl2,
        k - 1,
        1
      )

      for (_ <- 1 until n) {
        var n2 = State(
          kl,
          kl2,
          sub(
            next.sum,
            // conflict: c|c, c/c1|c, c1/c|c
            (next.vertical + ((next.horizontal * (kl - 1)) << 1)) % m
          ),
          sub(
            current.sum,
            // conflict: c1|c1/c2, c2|c1/c2, c1/c3|c1/c2, c3/c2|c1/c2, c1/c2|c1/c2
            ((current.vertical << 1) + current.horizontal * (kl - 2 + kl - 2 + 1)) % m
          )
        );
        current = next
        next = n2
      }
      current.sum.toInt
    }
  }
}
