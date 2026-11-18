/**
 * Helpers for the oracle tests (reasoner#45): compile a `.bend` file in this
 * directory with `bend -o` and import the resulting ES module.
 */
import { assert } from "@std/assert";

// deno-lint-ignore no-explicit-any -- the generated module is untyped
export type Bend = any;

/** hasBend reports whether the `bend` binary is on the PATH. */
export function hasBend(): boolean {
  try {
    return new Deno.Command("bend", {
      args: ["--help"],
      stdout: "null",
      stderr: "null",
    }).outputSync().success;
  } catch {
    return false;
  }
}

/** load compiles `file` (relative to this directory) and imports its defs. */
export async function load(file: string): Promise<Bend> {
  const dir = await Deno.makeTempDir();
  const out = `${dir}/model.mjs`;
  const src = new URL(`./${file}`, import.meta.url).pathname;
  const run = await new Deno.Command("bend", {
    args: [src, "-o", out],
    env: { BEND_NO_TELEMETRY: "1" },
  }).output();
  assert(run.success, new TextDecoder().decode(run.stderr));
  return (await import(`file://${out}`)).default;
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
