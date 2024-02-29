pub fn balanced_parens(n: u16) -> Vec<String> {
    let n = n as usize;
    let mut ret = Vec::with_capacity(n + 1);
    ret.push(Vec::from([String::new()]));
    for i in 1..=n {
        let mut v = Vec::new();
        for j in 1..=i {
            v.extend(
                ret[j - 1]
                    .iter()
                    .flat_map(|h| ret[i - j].iter().map(move |t| format!("({}){}", h, t))),
            );
        }
        ret.push(v)
    }
    ret.pop().unwrap()
}
