pub fn partitions(n: u32) -> u32 {
    let mut ret = vec![1; (n + 1) as usize];
    for i in 2..=n as usize {
        for j in i..=n as usize {
            ret[j] += ret[j - i];
        }
    }
    ret[n as usize]
}
