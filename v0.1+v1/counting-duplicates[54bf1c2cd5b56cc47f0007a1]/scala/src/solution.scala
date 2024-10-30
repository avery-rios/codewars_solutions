object Dups {

  def duplicateCount(str: String): Int =
    var mp = Array.fill(256)(0)
    str
      .chars()
      .filter(Character.isLetterOrDigit)
      .map(_.toChar.toLower)
      .forEach({ c => mp(c) += 1 })
    mp.count({ _ > 1 })
}
