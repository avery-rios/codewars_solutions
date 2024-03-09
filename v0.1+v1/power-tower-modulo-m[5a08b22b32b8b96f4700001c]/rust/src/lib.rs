struct Primes(Vec<u32>);

fn isqrt(m: u32) -> u32 {
    (m as f64).sqrt().ceil() as u32
}

fn primes(mx: u32) -> Primes {
    let max = isqrt(mx);
    let mut ret = Vec::with_capacity(max as usize + 1);
    let mut min_div = Vec::new();
    min_div.resize(max as usize + 1, 0);
    for i in 2..=max {
        let si = i as usize;
        if min_div[si] == 0 {
            min_div[si] = i;
            ret.push(i);
        }
        let md = min_div[si];
        for j in ret.iter().copied().take_while(|j| *j <= md) {
            let v = (j as u64) * (i as u64);
            if v > max as u64 {
                break;
            } else {
                min_div[v as usize] = j;
            }
        }
    }
    Primes(ret)
}

fn phi(ps: &Primes, m: u32) -> u32 {
    let mut num = 1;
    let mut de = 1;
    let mut n = m;
    let max_i = isqrt(m);
    for i in ps.0.iter().copied().take_while(|i| *i <= max_i) {
        if n % i == 0 {
            de *= i;
            num *= i - 1;
            while n % i == 0 {
                n /= i;
            }
        }
    }
    if n > 1 {
        de *= n;
        num *= n - 1;
    }
    (m / de) * num
}

fn pow(base: u64, mut e: u32, m: u32) -> (bool, u32) {
    type N = (bool, u64);
    const fn mul(l: N, r: N, m: u64) -> N {
        if l.0 || r.0 {
            (true, (l.1 * r.1) % m)
        } else {
            let p = l.1 * r.1;
            if p >= m {
                (true, p % m)
            } else {
                (false, p)
            }
        }
    }
    let mut ret = (false, 1);
    let m = m as u64;
    let mut base = if base >= m {
        (true, base % m)
    } else {
        (false, base)
    };
    while e > 0 {
        if e & 1 != 0 {
            ret = mul(ret, base, m);
        }
        base = mul(base, base, m);
        e >>= 1;
    }
    (ret.0, ret.1 as u32)
}

/// returns if value is greater of equal than m
fn tower_w(ps: &Primes, base: u64, h: u64, m: u32) -> (bool, u32) {
    if m == 1 {
        return (true, 0);
    }
    if h == 1 {
        let m = m as u64;
        if base >= m {
            (true, (base % m) as u32)
        } else {
            (false, base as u32)
        }
    } else {
        let pm = phi(ps, m);
        let (gt, tp) = tower_w(ps, base, h - 1, pm);
        if gt {
            (true, pow(base, tp + pm, m).1)
        } else {
            pow(base, tp, m)
        }
    }
}

pub fn tower(base: u64, h: u64, m: u32) -> u32 {
    if m == 1 {
        return 0;
    }
    if base == 1 {
        return 1;
    }
    if h == 0 {
        return 1;
    }
    tower_w(&primes(m), base, h, m).1
}
