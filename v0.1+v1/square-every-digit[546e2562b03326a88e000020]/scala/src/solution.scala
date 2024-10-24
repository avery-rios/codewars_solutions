def squareDigits(n: Int): Int = {
  var ret = 0
  var v = n
  var pow = 1
  while (v != 0) do
    val d = v % 10
    v = v / 10
    ret += d * d * pow
    pow *= (if d < 4 then 10 else 100)
  ret
}
