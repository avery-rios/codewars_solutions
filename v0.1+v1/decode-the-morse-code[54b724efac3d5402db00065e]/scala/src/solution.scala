object MorseDecoder {
  import MorseCodes.morseCodes

  def decode(msg: String) = msg
    .trim()
    .split("   ")
    .map({ _.split(" ").map(morseCodes).mkString })
    .mkString(" ")
}
