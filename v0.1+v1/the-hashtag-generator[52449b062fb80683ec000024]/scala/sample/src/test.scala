class HashTagSpec extends org.scalatest.flatspec.AnyFlatSpec {
  "generateHashtag" should "pass basic tests" in {
    assertResult("", "\nEmpty string should be returned for empty input string\nInput\n  s = \"\"") (generateHashtag(""))
    assertResult("", s"\nEmpty string should be returned if final word is over 140 chars\nInput\n  s = \"${"a" * 200}\"") (generateHashtag("a" * 200))
    assertResult("#Codewars", "\nInput\n  s = \"codewars\"") (generateHashtag("codewars"))
    assertResult("#ShouldRemoveSpaces", "\nInput\n  s = \"should remove spaces\"") (generateHashtag("should remove spaces"))
    assertResult("#RemoveDoubleSpaces", "\nInput\n  s = \"remove  double  spaces\"") (generateHashtag("remove  double  spaces"))
    assertResult("#RemoveUnneededCaps", "\nInput\n  s = \"rEMOVE uNNEEDED cAPS\"") (generateHashtag("rEMOVE uNNEEDED cAPS"))
    assertResult("#TrailingSpaces", "\nInput\n  s = \"Trailing spaces     \"") (generateHashtag("Trailing spaces     "))
    assertResult("#LeadingSpaces", "\nInput\n  s = \"     leading Spaces\"") (generateHashtag("     leading Spaces"))
    assertResult("#AcronymsShouldWorkASW", "\nInput\n  s = \"acronyms should work a s w\"") (generateHashtag("acronyms should work a s w"))
  }
}