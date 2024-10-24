export function descendingOrder(n: number): number {
  return Number.parseInt(Array.from(n.toString()).sort().reverse().join(""));
}
