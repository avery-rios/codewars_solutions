import scala.collection.mutable.StringBuilder
import scala.annotation.tailrec

@tailrec
private def iter(i: Int, digits: String): Option[Long] =
  if i < 0 then None
  else if digits(i) > digits(i + 1) then
    val vi = digits(i)
    val (l, pr) = digits.splitAt(i)
    val r = pr.drop(1)
    val idx = r.indexWhere({ vi <= _ }) match
      case -1 => r.length() - 1
      case i  => i - 1
    val s =
      (l :+ r(idx)) ++ r.drop(idx + 1).reverse ++ (r.take(idx) :+ vi).reverse
    if s(0) != '0'
    then Some(s.toLong)
    else None
  else iter(i - 1, digits)

def nextSmaller(n: Long): Option[Long] =
  val digits = n.toString()
  iter(digits.length() - 2, digits)
