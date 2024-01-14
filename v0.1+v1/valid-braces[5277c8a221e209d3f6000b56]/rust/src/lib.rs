#[derive(PartialEq, Eq)]
enum Brace {
    Paren,
    Bracket,
    Brace,
}

pub fn valid_braces(s: &str) -> bool {
    let mut stk = Vec::with_capacity(s.len());
    for i in s.chars() {
        match i {
            '(' => stk.push(Brace::Paren),
            '[' => stk.push(Brace::Bracket),
            '{' => stk.push(Brace::Brace),
            ')' => {
                if stk.pop() != Some(Brace::Paren) {
                    return false;
                }
            }
            ']' => {
                if stk.pop() != Some(Brace::Bracket) {
                    return false;
                }
            }
            '}' => {
                if stk.pop() != Some(Brace::Brace) {
                    return false;
                }
            }
            _ => (),
        }
    }
    stk.is_empty()
}