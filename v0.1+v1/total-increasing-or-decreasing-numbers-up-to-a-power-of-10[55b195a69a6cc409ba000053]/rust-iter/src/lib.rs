use std::mem::swap;

fn total_inc(n: u32) -> u64 {
    let mut c0 = [1u64; 10];
    let mut c1 = [0u64; 10];
    let mut cur = &mut c0;
    let mut lst = &mut c1;
    // add number to left
    for _ in 2..=n {
        swap(&mut cur, &mut lst);
        for d in 0..10 {
            cur[d] = lst[d..10].iter().sum();
        }
    }
    cur.iter().sum()
}

fn total_dec(n: u32) -> u64 {
    let mut c0 = [1u64; 10];
    let mut c1 = [0u64; 10];
    let mut cur = &mut c0;
    let mut lst = &mut c1;
    let mut ret = 10;
    // add number to left
    for _ in 2..=n {
        swap(&mut cur, &mut lst);
        for d in 0..10 {
            let v = lst[0..=d].iter().sum();
            cur[d] = v;
            ret += v; // number of length i
        }
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
