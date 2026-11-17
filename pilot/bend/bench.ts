/**
 * Times one closure of the `plain` bench profile (reasoner#39, Phase 4 harness;
 * Phase 1 uses the `reference` row). One size per process, so peak RSS belongs
 * to that run alone.
 *
 *     deno run --allow-read pilot/bend/bench.ts --impl reference --size 1e5
 *
 * Prints one JSON line: encode and closure milliseconds, closure size, rounds,
 * and peak RSS in MB (VmHWM on Linux).
 */
import { parseArgs } from "@std/cli/parse-args";
import { generate } from "../../bench/scaling.ts";
import { encode } from "./encode.ts";
import { closure } from "./reference.ts";

function peakRssMb(): number {
  try {
    const status = Deno.readTextFileSync("/proc/self/status");
    const match = /VmHWM:\s+(\d+) kB/.exec(status);
    if (match) return Math.round(Number(match[1]) / 1024);
  } catch {
    // Not Linux; fall back to the current RSS.
  }
  return Math.round(Deno.memoryUsage().rss / 1024 / 1024);
}

const args = parseArgs(Deno.args, {
  string: ["impl", "size"],
  default: { impl: "reference", size: "1e4" },
});
if (args.impl !== "reference") throw new Error(`unknown --impl ${args.impl}`);

const quads = generate(Number(args.size), "plain");
let start = performance.now();
const { triples } = encode(quads);
const encodeMs = performance.now() - start;
start = performance.now();
const result = closure(triples);
const closureMs = performance.now() - start;

console.log(JSON.stringify({
  impl: args.impl,
  asserted: quads.length,
  closure: result.triples.length / 3,
  rounds: result.rounds,
  encodeMs: Math.round(encodeMs),
  closureMs: Math.round(closureMs),
  rssMb: peakRssMb(),
}));
