export const pigIt = (a: string): string =>
  a
    .split(" ")
    .map((s) => {
      if (s.match(/[a-zA-Z]/)) {
        return s.substring(1) + s[0] + "ay";
      } else {
        return s;
      }
    })
    .join(" ");
