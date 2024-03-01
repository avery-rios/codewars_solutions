fn total_inc(n: u32) -> u64 {
    let mut ret = [1u64; 10];
    // add number to left
    for _ in 2..=n {
        for d in (0..9).rev() {
            ret[d] += ret[d + 1]
        }
    }
    ret.iter().sum()
}

fn total_dec(n: u32) -> u64 {
    let mut c = [1u64; 10];
    let mut ret = 10;
    // add number to left
    for _ in 2..=n {
        for d in 1..10 {
            c[d] += c[d - 1];
            ret += c[d];
        }
        ret += c[0];
    }
    ret
}

pub fn total_inc_dec(n: u32) -> u64 {
    if n == 0 {
        return 1;
    }
    // number that all digits is same is counted twice
    total_inc(n) + total_dec(n) - 10 * (n as u64)
}
