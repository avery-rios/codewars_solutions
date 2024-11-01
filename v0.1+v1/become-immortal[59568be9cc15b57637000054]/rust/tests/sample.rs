#[cfg(feature = "local")]
use become_immortal::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn example_tests() {
        assert_eq!(elder_age(8, 5, 1, 100), 5);
        assert_eq!(elder_age(8, 8, 0, 100007), 224);
        assert_eq!(elder_age(25, 31, 0, 100007), 11925);
        assert_eq!(elder_age(5, 45, 3, 1000007), 4323);
        assert_eq!(elder_age(31, 39, 7, 2345), 1586);
        assert_eq!(elder_age(545, 435, 342, 1000007), 808451);

        // You need to run this test very quickly before attempting the actual tests :)
        assert_eq!(elder_age(28827050410, 35165045587, 7109602, 13719506), 5456283);
    }
}   