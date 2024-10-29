export function findOutlier(integers: number[]): number {
  switch (
  integers
    .slice(0, 3)
    .map((v) => Math.abs(v) & 1)
    .reduce((p, v) => p + v)
  ) {
    case 0:
    case 1:
      return integers.find((v) => (v & 1) != 0)!;
    default:
      return integers.find((v) => (v & 1) == 0)!;
  }
}
