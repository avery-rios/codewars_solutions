#[cfg(feature = "local")]
use challenge::*;

#[cfg(test)]

mod tests {
    use super::next_bigger_number;
    
    const ERR_MSG: &str = "\nYour result (left) did not match the expected result (right).";
    
    #[test]
    fn sample_tests() {
        assert_eq!(next_bigger_number(9),    None,      "{ERR_MSG}");
        assert_eq!(next_bigger_number(12),   Some(21),  "{ERR_MSG}");
        assert_eq!(next_bigger_number(513),  Some(531), "{ERR_MSG}");
        assert_eq!(next_bigger_number(2017), Some(2071),"{ERR_MSG}");
        assert_eq!(next_bigger_number(414),  Some(441), "{ERR_MSG}");
        assert_eq!(next_bigger_number(144),  Some(414), "{ERR_MSG}");
    }
}
