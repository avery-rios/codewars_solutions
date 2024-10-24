def zeros(n: Int): Int = {
  var factor5 = 0
  var i = n
  while i >= 5 do
    val j = i / 5
    factor5 += j
    i = j
  factor5
}
