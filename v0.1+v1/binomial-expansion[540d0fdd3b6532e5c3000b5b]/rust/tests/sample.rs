#[cfg(feature = "local")]
use challenge::*;

#[cfg(test)]
mod tests {
    use super::expand;

    fn dotest(expr: &str, expected: &str) {
        let actual = expand(expr);
        assert!(
            actual == expected,
            "With expr = \"{expr}\"\nExpected \"{expected}\" but got \"{actual}\""
        )
    }

    #[test]
    fn fixed_tests() {
        dotest("(x+1)^0", "1");
        dotest("(x+1)^1", "x+1");
        dotest("(x+1)^2", "x^2+2x+1");
        dotest("(x-1)^0", "1");
        dotest("(x-1)^1", "x-1");
        dotest("(x-1)^2", "x^2-2x+1");
        dotest("(5m+3)^4", "625m^4+1500m^3+1350m^2+540m+81");
        dotest("(2x-3)^3", "8x^3-36x^2+54x-27");
        dotest("(7x-7)^0", "1");
        dotest("(-5m+3)^4", "625m^4-1500m^3+1350m^2-540m+81");
        dotest("(-2k-3)^3", "-8k^3-36k^2-54k-27");
        dotest("(-7x-7)^0", "1");
    }
}
