import org.junit.Test;
import static org.junit.Assert.assertEquals;

public class ExTests {

    @Test
    public void a_test_of_0() {
        String s = "This is a string exemplification!";
        String a = s;
        assertEquals(a, JomoPipi.stringFunc(s, 0));
    }

    @Test
    public void a_1st_test() {
        String s = "String for test: incommensurability";
        String a = "ySttirliinbga rfuosrn etmemsotc:n i";
        assertEquals(a, JomoPipi.stringFunc(s, 1));
    }

    @Test
    public void a_2nd_test() {
        String s = "Ohh Man God Damn";
        String a = " nGOnmohaadhMD  ";
        assertEquals(a, JomoPipi.stringFunc(s, 7));
    }

    @Test
    public void a_3rd_test() {
        String s = "Ohh Man God Damnn";
        String a = "haG mnad MhO noDn";
        assertEquals(a, JomoPipi.stringFunc(s, 19));
    }
}