
public class MorseCodeDecoder {
    public static String decode(String morseCode) {
        var ret = new StringBuilder();
        final String[] words = morseCode.strip().split("   ");
        for (int i = 0; i < words.length; ++i) {
            for (final var ch : words[i].split(" ")) {
                ret.append(MorseCode.get(ch));
            }
            if (i != words.length - 1) {
                ret.append(' ');
            }
        }
        return ret.toString();
    }
}