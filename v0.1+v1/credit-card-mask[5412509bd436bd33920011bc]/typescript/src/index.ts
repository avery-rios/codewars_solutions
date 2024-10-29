// return masked string
export function maskify(cc: string): string {
  if (cc.length <= 4) {
    return cc;
  } else {
    return cc.slice(cc.length - 4).padStart(cc.length, "#");
  }
}
