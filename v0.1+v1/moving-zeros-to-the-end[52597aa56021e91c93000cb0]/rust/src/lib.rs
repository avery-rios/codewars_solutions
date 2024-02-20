pub fn move_zeros(arr: &[u8]) -> Vec<u8> {
    let mut ret = Vec::with_capacity(arr.len());
    ret.extend(arr.iter().copied().filter(|v| *v != 0));
    ret.resize(arr.len(), 0);
    ret
}
