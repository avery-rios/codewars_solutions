def generateHashtag(s: String): String =
  val ret = s
    .split(" ")
    .flatMap({ word =>
      word.length() match {
        case 0 => Seq()
        case 1 => Seq(word(0).toUpper)
        case _ => Seq(word(0).toUpper, word.substring(1).map(_.toLower))
      }
    })
    .prepended("#")
    .mkString
  if s.isEmpty() || ret.length > 141 || ret.length() == 1 then "" else ret
