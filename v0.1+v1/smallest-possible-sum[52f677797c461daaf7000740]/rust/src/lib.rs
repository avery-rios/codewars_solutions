pub fn solution(arr: &[u64]) -> u128 {
    match arr.split_first() {
        Some((head, tail)) => {
            (arr.len() as u128) * (tail.iter().copied().fold(*head, num::integer::gcd) as u128)
        }
        None => 0,
    }
}
