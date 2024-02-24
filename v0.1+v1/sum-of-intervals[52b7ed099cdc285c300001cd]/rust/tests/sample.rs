#[cfg(feature = "local")]
use challenge::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html

#[cfg(test)]
mod sample_tests {
    use super::*;
    const ERR_MSG: &str = "\nYour result (left) did not match expected output (right).";
    
    #[test]
    fn non_overlapping_intervals() {
        assert_eq!(sum_intervals(&[(1, 5)]), 4, "{}", ERR_MSG);
        assert_eq!(sum_intervals(&[(1, 5), (6, 10)]), 8, "{}", ERR_MSG);
    }
    
    #[test]
    fn overlapping_intervals() {
        assert_eq!(sum_intervals(&[(1, 5), (1, 5)]), 4, "{}", ERR_MSG);
        assert_eq!(sum_intervals(&[(1, 4), (7, 10), (3, 5)]), 7, "{}", ERR_MSG);
    }
    
    #[test]
    fn large_intervals() {
        assert_eq!(sum_intervals(&[(-1_000_000_000, 1_000_000_000)]), 2_000_000_000, "{}", ERR_MSG);
        assert_eq!(sum_intervals(&[(0, 20), (-100_000_000, 10), (30, 40)]), 100_000_030, "{}", ERR_MSG);
    }
}