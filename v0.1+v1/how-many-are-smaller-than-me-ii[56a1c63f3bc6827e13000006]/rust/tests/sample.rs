#[cfg(feature = "local")]
use how_many_are_smaller_than_me_ii::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html

#[cfg(test)]
mod tests {
    use super::smaller;
    
    fn do_test(xs: &[i32], expected: &[usize]) {
        let actual = smaller(xs);
        assert_eq!(actual, expected, "\nYour result (left) did not match the expected output (right) for the input:\n{xs:?}")
    }

    #[test]
    fn sample_tests() {
        do_test(&[5, 4, 3, 2, 1], &[4, 3, 2, 1, 0]);
        do_test(&[1, 2, 3], &[0, 0, 0]);
        do_test(&[1, 2, 0], &[1, 1, 0]);
        do_test(&[1, 2, 1], &[0, 1, 0]);
        do_test(&[1, 1, -1, 0, 0], &[3, 3, 0, 0, 0]);
        do_test(&[5, 4, 7, 9, 2, 4, 4, 5, 6], &[4, 1, 5, 5, 0, 0, 0, 0, 0]);
        do_test(&[5, 4, 7, 9, 2, 4, 1, 4, 5, 6], &[5, 2, 6, 6, 1, 1, 0, 0, 0, 0]);
    }
}