export function duplicateEncode(word: string) {
  var s: Map<string, number> = new Map();
  for (const c of word) {
    const lc = c.toLowerCase();
    const cnt = s.get(lc);
    if (cnt == undefined) {
      s.set(lc, 1);
    } else {
      s.set(lc, cnt + 1);
    }
  }
  return Array.from(word)
    .map((c) => {
      if (s.get(c.toLowerCase())! == 1) {
        return "(";
      } else {
        return ")";
      }
    })
    .join("");
}
