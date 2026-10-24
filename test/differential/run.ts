// Usage: deno task test:differential [--seeds N] [--graph-stride K] [--verbose]
// Exits 1 when a failure class is not in expected-failures.json, or when a
// pinned repro in it no longer fails with its class (so the list cannot rot).
import { classify, diff, fmt, MODES, runSeed } from "./differential.ts";
import type { Failure, Mode, T3 } from "./differential.ts";

const at = Deno.args.indexOf("--seeds");
const SEEDS = at >= 0 ? Number(Deno.args[at + 1]) : 1000;
// The named-graph modes build a reasoner per graph and cost about ten times
// the others, so by default they run on every third seed; --graph-stride 1
// runs them on every seed.
const strideAt = Deno.args.indexOf("--graph-stride");
const STRIDE = strideAt >= 0 ? Number(Deno.args[strideAt + 1]) : 3;
const verbose = Deno.args.includes("--verbose");
interface Expected {
  mode?: Mode;
  issue: string;
  rules: string[];
  note: string;
  base: T3[];
  delta: T3[];
}
const expected: Record<string, Expected> = JSON.parse(
  Deno.readTextFileSync(new URL("./expected-failures.json", import.meta.url)),
);

const classes = new Map<string, { count: number; smallest: Failure }>();
for (let seed = 1; seed <= SEEDS; seed++) {
  for (const mode of MODES) {
    if (/^(union|graphs)-/.test(mode) && seed % STRIDE !== 0) continue;
    const f = runSeed(seed, mode);
    if (f === null) continue;
    const c = classes.get(f.cls);
    if (!c) classes.set(f.cls, { count: 1, smallest: f });
    else {
      c.count++;
      const size = (x: Failure) => x.base.length + x.delta.length;
      if (size(f) < size(c.smallest)) c.smallest = f;
    }
  }
}

console.log(`${SEEDS} seeds, ${classes.size} failure class(es)`);
let bad = false;
for (const [cls, { count, smallest }] of classes) {
  const known = cls in expected;
  console.log(`\n${known ? "KNOWN" : "NEW"} ${cls}: ${count} seed(s)`);
  if (known && !verbose) continue;
  console.log(
    `smallest repro, seed ${smallest.seed}\nbase:\n${fmt(smallest.base)}`,
  );
  console.log(`delta:\n${fmt(smallest.delta)}`);
  console.log(JSON.stringify(smallest.diff, null, 1));
  if (!known) bad = true;
}
// Each pinned repro must still fail with exactly its class, so a fix shows up
// as a stale entry even when the random seeds happen to miss it.
for (const [cls, e] of Object.entries(expected)) {
  const mode = e.mode ?? "extend";
  const d = diff(e.base, e.delta, mode);
  if (d === null || `${mode}: ${classify(d)}` !== cls) {
    console.log(`\nSTALE pinned repro (now ${d && classify(d)}): ${cls}`);
    bad = true;
  }
}
Deno.exit(bad ? 1 : 0);
