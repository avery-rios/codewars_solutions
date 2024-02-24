pub fn sum_intervals(intervals: &[(i32, i32)]) -> i32 {
    let intervals = {
        let mut i = intervals.to_vec();
        i.sort();
        i
    };
    if let Some((r0, rs)) = intervals.split_first() {
        let mut ret = r0.1 - r0.0;
        let mut r = r0.1;
        for i in rs.iter() {
            if r < i.1 {
                ret += i.1 - std::cmp::max(i.0, r);
                r = i.1;
            }
        }
        ret
    } else {
        0
    }
}
