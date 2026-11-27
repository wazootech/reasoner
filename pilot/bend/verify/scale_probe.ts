/**
 * Probe, not a test (reasoner#45, phase 12): how the Bend model scales on the
 * `plain` bench profile, naive and semi-naive, against the TypeScript
 * reference. Needs `bend` on the PATH.
 *
 *     bun pilot/bend/verify/scale_probe.ts 100 200 400
 */
import process from "node:process";
import { generate } from "../../../bench/scaling.ts";
import { encode } from "../encode.ts";
import { closure } from "../reference.ts";
import { closeModel, closeSemi, load } from "./bend_util.ts";

const bend = await load("rl.bend");
const time = (f: () => number): string => {
  const t = performance.now();
  try {
    const n = f();
    return `${(performance.now() - t).toFixed(0)} ms (${n} triples)`;
  } catch (e) {
    return `failed: ${(e as Error).message.slice(0, 40)}`;
  }
};
for (const size of process.argv.slice(2).map(Number)) {
  const { triples } = encode(generate(size, "plain"));
  const cells = [
    `reference ${time(() => closure(triples).triples.length / 3)}`,
    `semi-naive ${time(() => closeSemi(bend, triples, 20).length / 3)}`,
  ];
  if (size <= 200) {
    cells.push(`naive ${time(() => closeModel(bend, triples, 20).length / 3)}`);
  }
  console.log(
    `size ${size} (${triples.length / 3} asserted): ${cells.join("; ")}`,
  );
}
