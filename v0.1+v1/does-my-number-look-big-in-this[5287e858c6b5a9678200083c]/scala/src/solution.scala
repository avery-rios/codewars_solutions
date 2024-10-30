import java.util.ArrayList
import scala.collection.mutable.ArrayBuilder

object Kata {
  private def toDigits(n: Int): Array[Int] = {
    var ret = ArrayBuilder.ofInt();
    var i = n;
    while (i != 0) {
      ret.addOne(i % 10);
      i /= 10;
    }
    ret.result()
  }
  private def pow(n: Int, e: Int) = {
    var ret = 1;
    var p = n;
    var ex = e;
    while (ex != 0) {
      if ((ex & 1) == 1) {
        ret *= p;
      }
      p = p * p;
      ex >>= 1;
    }
    ret
  }

  def narcissistic(n: Int): Boolean = {
    val digits = toDigits(n);
    digits.map({ d => pow(d, digits.length) }).sum == n
  }
}
