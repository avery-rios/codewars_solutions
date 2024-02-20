pub fn snail(matrix: &[Vec<i32>]) -> Vec<i32> {
    let size = match matrix.first() {
        Some(v) => {
            if v.len() == 0 {
                return Vec::new();
            } else {
                v.len()
            }
        }
        None => return Vec::new(),
    };
    let mut ret = Vec::new();
    let mut off = 0;
    let mut n = size;
    while n > 0 {
        match n {
            0 => break,
            1 => {
                ret.push(matrix[off][off]);
                break;
            }
            _ => {
                let right = size - off;
                ret.extend_from_slice(&matrix[off][off..(right - 1)]); // upper
                ret.extend(matrix[off..(right - 1)].iter().map(|v| v[right - 1])); // right
                ret.extend(matrix[right - 1][(off + 1)..right].iter().rev()); // lower
                ret.extend(matrix[(off + 1)..right].iter().map(|v| v[off]).rev()); // left
                n -= 2;
                off += 1;
            }
        }
    }
    ret
}
