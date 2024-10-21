const MAX_DIGITS: usize = 20;
type Digits = [u8; MAX_DIGITS];

fn to_digits(mut n: u64) -> (usize, Digits) {
    let mut ret = [0; MAX_DIGITS];
    let mut pos = 0;
    while n > 0 {
        ret[pos] = (n % 10) as u8;
        n /= 10;
        pos += 1;
    }
    (pos, ret)
}
fn from_digits(digits: Digits) -> u64 {
    let mut ret = 0;
    for d in digits.into_iter().rev() {
        ret = ret * 10 + (d as u64);
    }
    ret
}

pub fn next_bigger_number(n: u64) -> Option<u64> {
    let (len, mut digits) = to_digits(n);
    for pos in 1..len {
        let val = digits[pos];
        if digits[pos - 1] > val {
            let left = digits[0..pos].partition_point(|x| *x <= val);
            digits.swap(left, pos);
            digits[0..pos].reverse();
            return Some(from_digits(digits));
        }
    }
    None
}
