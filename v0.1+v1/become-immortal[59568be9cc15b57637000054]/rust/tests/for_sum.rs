use become_immortal::elder_age;

fn sum(n: u64, m: u64, l: u64, t: u64) -> u64 {
    let mut ret = 0;
    for i in 0..n {
        for j in 0..m {
            ret += (i ^ j).saturating_sub(l) as u128;
        }
    }
    (ret % (t as u128)) as u64
}

fn test(n: u64, m: u64, l: u64, t: u64) {
    assert_eq!(
        elder_age(m, n, l, t),
        sum(n, m, l, t),
        "n={n} m={m} l={l} t={t}"
    );
}

#[test]
fn same_pow2() {
    test(4, 4, 2, 256)
}

#[test]
fn pow2() {
    test(4, 16, 3, 4096);
}

#[test]
fn same_non_pow2() {
    test(9, 9, 4, 4096);
}

#[test]
fn non_pow2() {
    test(9, 27, 5, 4096);
}

#[test]
fn fail_0() {
    test(98, 422, 3, 10512);
}

#[test]
fn fail_1() {
    test(491, 487, 8, 9786)
}

#[test]
fn fail_2() {
    test(331, 334, 11, 3543)
}
