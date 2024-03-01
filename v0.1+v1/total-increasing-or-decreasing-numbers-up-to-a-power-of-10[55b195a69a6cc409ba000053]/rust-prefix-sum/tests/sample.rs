#[cfg(feature = "local")]
use challenge::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html
#[cfg(test)]
mod tests {
    use super::total_inc_dec;
        
    fn dotest(n: u32, expected: u64) {
        let actual = total_inc_dec(n);
        assert!(actual == expected, "With n = {n}\nExpected {expected} but got {actual}")
    }

    #[test]
    fn fixed_tests() {
        dotest(0, 1);
        dotest(1, 10);
        dotest(2, 100);
        dotest(3, 475);
        dotest(4, 1675);
    }
}
