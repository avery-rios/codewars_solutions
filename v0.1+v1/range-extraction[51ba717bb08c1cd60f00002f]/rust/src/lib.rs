pub mod solution {
    use std::fmt::{self, Write};

    fn ranges(a: &[i32]) -> Vec<(i32, i32)> {
        let (mut last, a) = match a.split_first() {
            Some((i, a)) => ((*i, *i), a),
            None => return Vec::new(),
        };
        let mut ret = Vec::with_capacity(a.len());
        for i in a.iter().copied() {
            if i == last.1 + 1 {
                last.1 = i;
            } else {
                ret.push(last);
                last = (i, i);
            }
        }
        ret.push(last);
        ret
    }

    fn fmt_range(fmt: &mut String, r: (i32, i32)) -> fmt::Result {
        if r.0 == r.1 {
            write!(fmt, "{}", r.0)
        } else if r.0 + 1 == r.1 {
            write!(fmt, "{},{}", r.0, r.1)
        } else {
            write!(fmt, "{}-{}", r.0, r.1)
        }
    }

    pub fn range_extraction(a: &[i32]) -> String {
        let rs = ranges(a);
        let mut ret = String::new();
        if let Some((i, t)) = rs.split_last() {
            for r in t {
                fmt_range(&mut ret, *r).unwrap();
                ret.push(',');
            }
            fmt_range(&mut ret, *i).unwrap();
        }
        ret
    }
}
