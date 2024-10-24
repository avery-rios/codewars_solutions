public class PangramChecker {
  public boolean check(String sentence) {
    boolean[] letters = new boolean[26];

    for (int i = 0; i < sentence.length(); ++i) {
      final char c = sentence.charAt(i);
      if (Character.isAlphabetic(c)) {
        letters[Character.toLowerCase(c) - 'a'] = true;
      }
    }

    boolean ret = true;
    for (boolean b : letters) {
      ret &= b;
    }
    return ret;
  }
}