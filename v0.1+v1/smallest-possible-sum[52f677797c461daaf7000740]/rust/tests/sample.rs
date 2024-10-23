#[cfg(feature = "local")]
use smallest_possible_sum::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html

#[cfg(test)]
mod tests {
    use super::solution;

    #[test]
    fn fixed_tests() {
        assert_eq!(solution(&[1, 21, 55]), 3);
        assert_eq!(solution(&[3, 13, 23, 7, 83]), 5);
        assert_eq!(solution(&[4, 16, 24]), 12);
        assert_eq!(solution(&[30, 12]), 12);
        assert_eq!(solution(&[60, 12, 96, 48, 60, 24, 72, 36, 72, 72, 48]), 132);
        assert_eq!(solution(&[71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71, 71]), 923);
        assert_eq!(solution(&[11, 22]), 22);
        assert_eq!(solution(&[9]), 9);
        assert_eq!(solution(&[1]), 1);
        assert_eq!(solution(&[9, 9]), 18);
    }
}
