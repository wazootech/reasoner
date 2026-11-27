/**
 * Helpers for the oracle tests (reasoner#45): compile a `.bend` file in this
 * directory with `bend -o` and import the resulting ES module.
 */
import { spawnSync } from "node:child_process";
import { mkdtemp } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import process from "node:process";
import { fileURLToPath, pathToFileURL } from "node:url";
import { assert } from "../../../test/asserts.ts";

// `any` is allowed in this file only (.oxlintrc.json): the generated module
// is untyped.
export type Bend = any;

/** hasBend reports whether the `bend` binary is on the PATH. */
export function hasBend(): boolean {
  return spawnSync("bend", ["--help"], { stdio: "ignore" }).status === 0;
}

/** load compiles `file` (relative to this directory) and imports its defs. */
export async function load(file: string): Promise<Bend> {
  const dir = await mkdtemp(join(tmpdir(), "bend-"));
  const out = join(dir, "model.mjs");
  const src = fileURLToPath(new URL(`./${file}`, import.meta.url));
  const run = spawnSync("bend", [src, "-o", out], {
    encoding: "utf8",
    env: { ...process.env, BEND_NO_TELEMETRY: "1" },
  });
  assert(run.status === 0, run.stderr);
  return (await import(pathToFileURL(out).href)).default;
}

/** random returns a deterministic generator (mulberry32). */
export function random(seed: number): () => number {
  return () => {
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** toBend turns flat `[s, p, o, ...]` triples into the model's `Ts` list. */
export function toBend(flat: Uint32Array): unknown {
  let list: unknown = { $: "TNil" };
  for (let i = flat.length - 3; i >= 0; i -= 3) {
    list = {
      $: "TCons",
      h: { $: "T", s: flat[i], p: flat[i + 1], o: flat[i + 2] },
      t: list,
    };
  }
  return list;
}

/** fromBend turns the model's `Ts` list back into flat triples. */
export function fromBend(list: Bend): Uint32Array {
  const out: number[] = [];
  for (let l = list; l.$ === "TCons"; l = l.t) out.push(l.h.s, l.h.p, l.h.o);
  return Uint32Array.from(out);
}

/**
 * closeModel runs the model's rounds until its proved stop test passes, up to
 * `limit` rounds, and returns the result as flat triples. Round n+1 is
 * `step` of round n, which is how `iter` is defined; the test is the proved
 * `subset(step(r), r)`, reusing the `step` it computed.
 */
export function closeModel(
  bend: Bend,
  input: Uint32Array,
  limit: number,
): Uint32Array {
  let r = toBend(input);
  for (let rounds = 0; rounds <= limit; rounds++) {
    const next = bend.step(r);
    if (bend.subset(next, r) === true) return fromBend(r);
    r = next;
  }
  throw new Error(`no fixpoint within ${limit} rounds`);
}

/**
 * closeSemi runs the model's semi-naive rounds (`iter_semi`, state
 * `(old, delta)`) until `semi_delta` is empty, and returns the graph as flat
 * triples. Its stop test is `semi_fixed`, which RL_LAWS.bend proves means closed.
 */
export function closeSemi(
  bend: Bend,
  input: Uint32Array,
  limit: number,
): Uint32Array {
  let old: unknown = { $: "TNil" };
  let delta = toBend(input);
  for (let rounds = 0; rounds <= limit; rounds++) {
    const all = bend.append(delta, old);
    const d = bend.semi_delta(all, delta);
    if (d.$ === "TNil") return fromBend(all);
    old = all;
    delta = d;
  }
  throw new Error(`no fixpoint within ${limit} rounds`);
}
