use std::cmp::Ordering;

pub fn dbl_linear(n: u32) -> u32 {
    let mut ret = Vec::with_capacity(n as usize + 1);
    ret.push(1);
    let (mut p2, mut v2) = (0, 3);
    let (mut p3, mut v3) = (0, 4);
    for _ in 1..=n {
        let cp = v2.cmp(&v3);
        match cp {
            Ordering::Less => {
                ret.push(v2);
            }
            Ordering::Equal => {
                ret.push(v2);
            }
            Ordering::Greater => {
                ret.push(v3);
            }
        }
        if cp.is_le() {
            p2 += 1;
            v2 = ret[p2] * 2 + 1;
        }
        if cp.is_ge() {
            p3 += 1;
            v3 = ret[p3] * 3 + 1;
        }
    }
    ret.pop().unwrap()
}
