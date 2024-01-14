#[cfg(feature = "local")]
use challenge::*;

#[cfg(test)]
mod tests {
    use super::*; 

    #[test]
    fn basic_tests() {
        expect_true("()");
        expect_false("[(])");
    }
    
    fn expect_true(s: &str) {
        assert!(valid_braces(s), "Expected {s:?} to be valid. Got false", s=s);
    }
    
    fn expect_false(s: &str) {
        assert!(!valid_braces(s), "Expected {s:?} to be invalid. Got true", s=s);
    }
}