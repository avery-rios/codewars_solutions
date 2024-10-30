#[cfg(feature = "local")]
use path_finder_number_2_shortest_path::*;

// Add your tests here.
// See https://doc.rust-lang.org/stable/rust-by-example/testing/unit_testing.html

#[cfg(test)]
mod tests {
    use super::path_finder;


    #[test]
    fn fixed_tests() {
        assert_eq!(path_finder(".W.\n.W.\n..."), Some(4), "\nYour answer (left) is not the expected answer (right).");
        assert_eq!(path_finder(".W.\n.W.\nW.."), None, "\nYour answer (left) is not the expected answer (right).");
        assert_eq!(path_finder("......\n......\n......\n......\n......\n......"), Some(10), "\nYour answer (left) is not the expected answer (right).");
        assert_eq!(path_finder("......\n......\n......\n......\n.....W\n....W."), None, "\nYour answer (left) is not the expected answer (right).");
    }
}
