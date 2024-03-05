use std::fmt::Write;

type Num = i32;

struct Expr {
    a: Num,
    x: char,
    b: Num,
    e: u32,
}
impl Expr {
    fn from_str(s: &str) -> Self {
        let s = s.strip_prefix('(').unwrap();

        let pos = s.find(char::is_alphabetic).unwrap();
        let a = match &s[0..pos] {
            "" => 1,
            "-" => -1,
            sa => sa.parse().unwrap(),
        };
        let s = &s[pos..];

        let x = s.chars().next().unwrap();
        let s = &s[1..];

        let (sb, s) = s.split_once(")^").unwrap();
        Self {
            a,
            x,
            b: sb.parse().unwrap(),
            e: s.parse().unwrap(),
        }
    }
}

fn show_term(sign: bool, c: Num, x: char, e: u32, f: &mut String) {
    match c {
        1 if sign => f.push('+'),
        1 => (),
        -1 => f.push('-'),
        _ => {
            let _ = if sign {
                write!(f, "{c:+}")
            } else {
                write!(f, "{c}")
            };
        }
    }
    f.push(x);
    if e != 1 {
        let _ = write!(f, "^{e}");
    }
}

fn binomial(k: u32) -> Vec<Num> {
    let mut ret = Vec::with_capacity(k as usize + 1);
    ret.push(1);
    for i in 1..=k {
        for j in (1..i as usize).rev() {
            ret[j] += ret[j - 1];
        }
        ret.push(1);
    }
    ret
}
fn pow(a: Num, k: u32) -> Vec<Num> {
    let mut ret = Vec::with_capacity(k as usize + 1);
    ret.push(1);
    let mut acc = 1;
    for _ in 0..=k {
        acc *= a;
        ret.push(acc);
    }
    ret
}

pub fn expand(expr: &str) -> String {
    let e = Expr::from_str(expr);
    let bin = binomial(e.e);
    let ea = pow(e.a, e.e);
    let eb = pow(e.b, e.e);

    let mut sign = false;
    let mut ret = String::new();
    let sk = e.e as usize;
    for i in (1..=e.e).rev() {
        let si = i as usize;
        let c = bin[si] * ea[si] * eb[sk - si];
        if c != 0 {
            show_term(sign, c, e.x, i, &mut ret);
            sign = true;
        }
    }
    {
        let c = eb[sk];
        if c != 0 {
            let _ = if sign {
                write!(ret, "{c:+}")
            } else {
                write!(ret, "{c}")
            };
        }
    }
    ret
}
