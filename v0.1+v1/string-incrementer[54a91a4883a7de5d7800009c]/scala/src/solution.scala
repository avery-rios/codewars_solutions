import scala.math.max
def incrementString(s: String): String =
  val (letters, digits) = s.splitAt(s.lastIndexWhere({ !_.isDigit }) match {
    case -1 => 0
    case l  => l + 1
  })
  val n = if digits.isEmpty() then 0 else digits.toInt
  val ns = (n + 1).toString()
  letters ++ "0" * max(digits.length() - ns.length(), 0) ++ ns
