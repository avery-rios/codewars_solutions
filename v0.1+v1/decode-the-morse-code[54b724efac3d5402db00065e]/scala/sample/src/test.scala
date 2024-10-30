import org.scalatest._
import flatspec._

class ExampleTest extends AnyFlatSpec {

  import MorseDecoder.decode

  val testCases = List( //(description, input, expected)
    ("the example from the description",".... . -.--   .--- ..- -.. .", "HEY JUDE")
    //add your test cases here
  )
  
  testCases.foreach {
    case (description, input, expected) => 
      s"$description" should s"return \"$expected\"" in {
        assertResult(expected) {decode(input)}
    }
  }
}