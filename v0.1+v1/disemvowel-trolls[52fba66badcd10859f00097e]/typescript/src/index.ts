export class Kata {
  static disemvowel(str: string): string {
    return str.replaceAll(/[aeiouAEIOU]/g, "");
  }
}
