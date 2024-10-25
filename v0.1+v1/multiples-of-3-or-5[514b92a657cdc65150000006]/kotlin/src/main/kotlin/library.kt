private fun sum_factor(number: Int, factor: Int): Int {
  val count = (number - 1) / factor
  return factor * count * (count + 1) / 2
}

fun solution(number: Int): Int {
  if (number < 0) {
    return 0
  } else {
    return sum_factor(number, 3) + sum_factor(number, 5) - sum_factor(number, 15)
  }
}
