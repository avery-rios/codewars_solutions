fn discrete(arr: &[i32]) -> (usize, Vec<u32>) {
    let elem = {
        let mut ret = arr.to_vec();
        ret.sort();
        ret.dedup();
        ret
    };
    (
        elem.len(),
        arr.iter()
            .map(|a| elem.binary_search(&a).unwrap() as u32 + 1)
            .collect(),
    )
}

#[inline]
const fn lowbit(x: usize) -> usize {
    x & x.wrapping_neg()
}
struct Count(Vec<u32>);
impl Count {
    fn new(size: usize) -> Self {
        Self(vec![0; size + 1])
    }
    fn add(&mut self, mut pos: usize) {
        while pos < self.0.len() {
            self.0[pos] += 1;
            pos += lowbit(pos);
        }
    }
    fn sum(&self, mut pos: usize) -> u32 {
        let mut ret = 0;
        while pos > 0 {
            ret += self.0[pos];
            pos -= lowbit(pos);
        }
        ret
    }
}

pub fn smaller(arr: &[i32]) -> Vec<usize> {
    let (distinct_cnt, arr) = discrete(arr);
    let mut count = Count::new(distinct_cnt);
    let mut ret = vec![0; arr.len()];
    for (idx, v) in arr.into_iter().enumerate().rev() {
        ret[idx] = count.sum(v as usize - 1) as usize;
        count.add(v as usize);
    }
    ret
}
