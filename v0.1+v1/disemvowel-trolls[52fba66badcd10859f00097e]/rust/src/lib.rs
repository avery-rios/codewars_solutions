pub fn disemvowel(s: &str) -> String {
    s.replace(['a', 'A', 'e', 'E', 'i', 'I', 'o', 'O', 'u', 'U'], "")
}
