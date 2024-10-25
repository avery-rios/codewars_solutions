public class FunReverse {

    public static String funReverse(String s) {
        StringBuilder ret = new StringBuilder();
        int start = 0;
        int end = s.length() - 1;
        for (; start < end; start++, end--) {
            ret.append(s.charAt(end));
            ret.append(s.charAt(start));
        }
        if (start == end) {
            ret.append(s.charAt(start));
        }
        return ret.toString();
    }
}