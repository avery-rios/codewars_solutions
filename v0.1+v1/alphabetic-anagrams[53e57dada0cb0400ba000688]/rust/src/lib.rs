const fn fac<const N: usize>() -> [u128; N] {
    let mut ret = [0; N];
    ret[0] = 1;
    let mut i = 1;
    while i < N {
        ret[i] = ret[i - 1] * i as u128;
        i += 1;
    }
    ret
}

const FAC: [u128; 26] = fac::<26>();

type CharCnt = [u8; 26];

fn lt_permu(len: usize, chr: u8, count: &CharCnt) -> u128 {
    let gt_permu = count[chr as usize..]
        .iter()
        .copied()
        .fold(FAC[len - 1], |acc, i| {
            if i == 0 {
                acc
            } else {
                acc / FAC[i as usize]
            }
        });
    let fac_r = {
        let mut v = [0; 26];
        v[(chr - 1) as usize] = 1;
        for i in (1..chr as usize).rev() {
            v[i - 1] = if count[i] != 0 {
                v[i] * FAC[count[i] as usize]
            } else {
                v[i]
            };
        }
        v
    };

    let mut ret = 0;
    let mut fac_l = 1;
    for i in 0..chr as usize {
        if count[i] != 0 {
            ret += gt_permu / fac_l / FAC[count[i] as usize - 1] / fac_r[i];
            fac_l *= FAC[count[i] as usize];
        }
    }
    ret
}

pub fn list_position(word: &str) -> u128 {
    let mut ccnt: CharCnt = [0; 26];
    for i in word.bytes() {
        ccnt[(i - b'A') as usize] += 1;
    }

    let mut ret = 1;
    let len = word.len();
    for (idx, c) in word.bytes().enumerate() {
        let c_idx = c - b'A';
        if c != b'A' {
            ret += lt_permu(len - idx, c_idx, &ccnt);
        }
        ccnt[c_idx as usize] -= 1;
    }
    ret
}
