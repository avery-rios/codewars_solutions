use std::num::NonZeroU64;

#[inline]
const fn lowbit(n: u64) -> u64 {
    n & n.wrapping_neg()
}

struct ModVal(u64);

#[inline]
const fn sum(l: u64, r: u64, t: NonZeroU64) -> ModVal {
    let v1 = l + r - 1;
    let v2 = r - l;
    let t = t.get();
    if v1 & 1 == 0 {
        ModVal(((v1 >> 1) % t * (v2 % t)) % t)
    } else {
        ModVal(((v1 % t) * ((v2 >> 1) % t)) % t)
    }
}
#[inline]
const fn mul_exp2(l: ModVal, mut e: u32, t: NonZeroU64) -> ModVal {
    let t = t.get();
    let mut ret = l.0;
    let pow63 = (1 << 63) % t;
    while e > 63 {
        ret = (ret * pow63) % t;
        e -= 63;
    }
    ModVal((ret * ((1 << e) % t)) % t)
}
#[inline]
fn sub(l: u64, r: u64, t: NonZeroU64) -> ModVal {
    ModVal((l as i64 - r as i64).rem_euclid(t.get() as i64) as u64)
}

/** result from `m..(m+lbm)` `n..(n+lbn)`

xor results contains three parts (len_m > len_n)
   - high: xor of high bits of m and n
   - middle: bits of m xor 0..2^(len_m-len_n)
   - low: xor of 0..2^len_n and 0..2^len_n
*/
fn xor_sum_u(m: u64, len_m: u64, n: u64, len_n: u64, l: u64, t: NonZeroU64) -> u64 {
    let (m, len_m, n, len_n) = if len_m > len_n {
        (m, len_m, n, len_n)
    } else {
        (n, len_n, m, len_m)
    };
    let lb_len_m = len_m.trailing_zeros();
    let lb_len_n = len_n.trailing_zeros();
    let high = (m ^ n) & !(len_m - 1);

    // high>=l, `middle` and `low` can be anything
    if high >= l {
        let lb_mid_count = lb_len_m - lb_len_n;
        let lb_low_count = lb_len_n + lb_len_n;

        let high_sum = mul_exp2(ModVal(high % t), lb_mid_count + lb_low_count, t);
        let mid_sum = mul_exp2(
            sum(0, 1 << (lb_len_m - lb_len_n), t),
            lb_len_n + lb_low_count,
            t,
        );
        let low_sum = mul_exp2(sum(0, 1 << lb_len_n, t), lb_len_n + lb_mid_count, t);

        sub(
            high_sum.0 + mid_sum.0 + low_sum.0,
            mul_exp2(ModVal(l % t), lb_mid_count + lb_low_count, t).0,
            t,
        )
        .0
    } else if high + len_m > l {
        // high+middle>=l, so `low` can be anything
        let mid_greater_sum = {
            let mid_min = ((l >> lb_len_n) & ((1 << (lb_len_m - lb_len_n)) - 1)) + 1;
            let mid_max = len_m >> lb_len_n;
            let mid_count = (mid_max - mid_min) % t;

            let lb_low_count = lb_len_n + lb_len_n;

            let high_sum = mul_exp2(ModVal((mid_count * (high % t)) % t), lb_low_count, t);
            let mid_sum = mul_exp2(sum(mid_min, mid_max, t), lb_len_n + lb_low_count, t);
            let low_sum = (mid_count * mul_exp2(sum(0, 1 << lb_len_n, t), lb_len_n, t).0) % t;

            sub(
                high_sum.0 + mid_sum.0 + low_sum,
                mid_count * mul_exp2(ModVal(l % t), lb_low_count, t).0,
                t,
            )
        };

        // high+middle is higher bits of l, `low` must be greater or equal than
        // low bits of l
        let mid_equal_sum = {
            let low_min = l & ((1 << lb_len_n) - 1);
            let low_max = 1 << lb_len_n;
            let low_count = (low_max - low_min) % t;

            let middle = (l >> lb_len_n) & ((1 << (lb_len_m - lb_len_n)) - 1);

            let high_mid_sum = mul_exp2(
                ModVal((((high | (middle << lb_len_n)) % t) * low_count) % t),
                lb_len_n,
                t,
            );
            let low_sum = mul_exp2(sum(low_min, low_max, t), lb_len_n, t);

            sub(
                high_mid_sum.0 + low_sum.0,
                mul_exp2(ModVal((l * low_count) % t), lb_len_n, t).0,
                t,
            )
        };
        mid_greater_sum.0 + mid_equal_sum.0
    } else {
        0
    }
}

struct IterBitsU(u64);
impl std::iter::Iterator for IterBitsU {
    type Item = (u64, u64);
    fn next(&mut self) -> Option<Self::Item> {
        if self.0 > 0 {
            let lb = lowbit(self.0);
            self.0 -= lb;
            Some((self.0, lb))
        } else {
            None
        }
    }
}

pub fn elder_age(m: u64, n: u64, l: u64, t: u64) -> u64 {
    let mut ret = 0;

    let t = NonZeroU64::new(t).unwrap();

    for (m, lm) in IterBitsU(m) {
        for (n, ln) in IterBitsU(n) {
            ret += xor_sum_u(m, lm, n, ln, l, t);
        }
    }

    ret % t
}
