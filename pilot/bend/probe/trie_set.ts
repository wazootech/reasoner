// Same 2.32M keys as trie.bend (8 chunks of 290000, same LCG and seed tree), into a JS Set.
const seeds: number[] = [];
function walk(s: number, seed: number): void {
  if (s === 0) {
    seeds.push(seed);
    return;
  }
  walk(s - 1, (seed * 2 + 1) >>> 0);
  walk(s - 1, (seed * 2 + 2) >>> 0);
}
walk(3, 1);
for (let run = 0; run < 3; run++) {
  const t0 = performance.now();
  const set = new Set<number>();
  for (const seed of seeds) {
    let s = seed;
    for (let n = 0; n < 290000; n++) {
      s = (Math.imul(s, 1664525) + 1013904223) >>> 0;
      set.add((s >>> 8) & 4194303);
    }
  }
  console.log(
    `distinct=${set.size} build_ms=${Math.round(performance.now() - t0)}`,
  );
}
