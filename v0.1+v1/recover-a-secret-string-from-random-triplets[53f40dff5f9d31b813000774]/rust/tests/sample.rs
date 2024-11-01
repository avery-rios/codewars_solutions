#[cfg(feature = "local")]
use recover_a_secret_string_from_random_triplets::*;

// Rust test example:
// TODO: replace with your own tests (TDD), these are just how-to examples.
// See: https://doc.rust-lang.org/book/testing.html

#[test]
fn example_test() {
  assert_eq!(recover_secret(vec![ 
  ['t','u','p'],
  ['w','h','i'],
  ['t','s','u'],
  ['a','t','s'],
  ['h','a','p'],
  ['t','i','s'],
  ['w','h','s']])
  , "whatisup");
}