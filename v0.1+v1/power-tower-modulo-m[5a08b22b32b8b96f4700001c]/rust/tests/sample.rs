#[cfg(feature = "local")]
use challenge::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn corner_cases() {
        assert_eq!(tower(10, 1, 4), 2);
        assert_eq!(tower(729, 0, 1), 0);
        assert_eq!(tower(729, 0, 2), 1);
        assert_eq!(tower(1, 897, 8934279), 1);
    }

    #[test]
    fn small_values() {
        assert_eq!(tower(3, 3, 25), 12);
        assert_eq!(tower(2, 2, 1000), 4);
        assert_eq!(tower(2, 3, 100000), 16);
        assert_eq!(tower(2, 4, 100000000), 65536);
        assert_eq!(tower(4, 2, 10000000), 256);
        assert_eq!(tower(4, 3, 10), 6);
        assert_eq!(tower(7, 1, 5), 2);
    }
    #[test]
    fn cannot_replace_base_with_base_modulo_m() {
        assert_ne!(tower(28, 3, 25), tower(28 % 25, 3, 25));
    }
    #[test]
    fn cannot_replace_the_exponent_with_exponent_modulo_m() {
        let base = 13_u64;
        let mut h = 3_u64;
        let m = 31_u32;
        let a = tower(base, h, m);
        h = 2;
        assert_ne!(a, ((13_u64).pow(tower(base, h, m)) as u32) % m);
    }
    #[test]
    fn however_there_are_cycles_in_the_exponent() {
        let a = tower(13, 3, 31);
        let b = tower(13, 2, 30);
        assert_eq!(a, (13_u64.pow(b) % 31) as u32);
    }
    #[test]
    fn pushing_to_the_limit_of_small() {
        assert_eq!(tower(3, 4, 1001), 482);
    }
    #[test]
    fn pushing_it_even_further() {
        assert_eq!(tower(2, 6, 1001), 471);
    }
}
