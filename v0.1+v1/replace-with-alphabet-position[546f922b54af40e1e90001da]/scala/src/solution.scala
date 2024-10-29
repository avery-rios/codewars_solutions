import scala.collection.mutable.StringBuilder
object Kata {

  def alphabetPosition(text: String): String =
    text
      .filter(Character.isLetter)
      .map({ c => (c.toLower - 'a').toInt + 1 })
      .mkString(" ")
}
