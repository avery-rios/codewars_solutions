#[cfg(feature = "local")]
use challenge::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html

#[cfg(test)]
mod tests {
    use super::balanced_parens;
    
    fn do_test(n: u16, expected: Vec<&str>) {
        let mut actual = balanced_parens(n);
        actual.sort();
        assert!(actual == expected, "With n = {n}\nExpected \"{expected:?}\"\nBut got \"{actual:?}\"");
    }
    
    #[test]
    fn sample_tests() {
        let tests = [
            (0, vec![""]),
            (1, vec!["()"]),
            (2, vec!["(())", "()()"]),
            (3, vec!["((()))", "(()())", "(())()", "()(())", "()()()"]),
        ];
        for (n, exp) in tests.iter() {
            do_test(*n, exp.to_vec())
        }
    }
}
