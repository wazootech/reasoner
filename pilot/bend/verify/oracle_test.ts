/**
 * Differential test (reasoner#45): the Bend model of scm-sco, whose laws are
 * proved in PROOF.bend, against the pilot's TypeScript reference closure on
 * random subClassOf graphs.
 *
 * The proofs say the model's `step` is exactly "the graph plus every
 * composition" and that a passing stop test means the result is closed. This
 * test connects that to the code in `reference.ts`: both must produce the same
 * subClassOf edges. It compiles `sco.bend` with `bend -o`, so it needs `bend`
 * on the PATH and is skipped without it.
 *
 *     bun test pilot/bend/verify/oracle_test.ts
 */
import { test } from "node:test";
import { assert, assertEquals } from "../../../test/asserts.ts";
import { V } from "../encode.ts";
import { type Bend, hasBend, load, random } from "./bend_util.ts";
import { closure } from "../reference.ts";

/** Edge is `[subclass, superclass]`; ids start at 10, clear of the vocabulary. */
type Edge = readonly [number, number];

function toList(edges: readonly Edge[]): unknown {
  return edges.reduceRight<unknown>(
    (t, [a, b]) => ({ $: "ECons", h: { $: "E", a, b }, t }),
    { $: "ENil" },
  );
}

function fromList(list: Bend): Set<string> {
  const out = new Set<string>();
  for (let l = list; l.$ === "ECons"; l = l.t) out.add(`${l.h.a} ${l.h.b}`);
  return out;
}

/** reference closes the edges with the TypeScript reference. */
function reference(edges: readonly Edge[]): Set<string> {
  const flat = new Uint32Array(edges.length * 3);
  edges.forEach(([a, b], i) => flat.set([a, V.subClassOf, b], i * 3));
  const out = new Set<string>();
  const { triples } = closure(flat);
  for (let i = 0; i < triples.length; i += 3) {
    if (triples[i + 1] === V.subClassOf) {
      out.add(`${triples[i]} ${triples[i + 2]}`);
    }
  }
  return out;
}

function length(list: Bend): number {
  let n = 0;
  for (let l = list; l.$ === "ECons"; l = l.t) n++;
  return n;
}

/** Result is the model's closure and how long its list is. */
interface Result {
  readonly edges: Set<string>;
  readonly listLength: number;
}

/** model runs rounds until the proved stop test passes, up to `limit`. */
function model(bend: Bend, edges: readonly Edge[], limit: number): Result {
  const start = toList(edges);
  for (let rounds = 0; rounds <= limit; rounds++) {
    const r = bend.iter(rounds, start);
    if (bend.subset(bend.step(r), r) === true) {
      return { edges: fromList(r), listLength: length(r) };
    }
  }
  throw new Error(`no fixpoint within ${limit} rounds`);
}

test("Bend scm-sco model matches the TypeScript reference on random graphs", {
  skip: !hasBend(),
}, async () => {
  const bend = await load("sco.bend");
  let grew = 0, cyclic = 0;
  for (let seed = 1; seed <= 500; seed++) {
    const rnd = random(seed);
    const nodes = 2 + Math.floor(rnd() * 7);
    const edges: Edge[] = Array.from(
      { length: Math.floor(rnd() * 13) },
      () =>
        [
          10 + Math.floor(rnd() * nodes),
          10 + Math.floor(rnd() * nodes),
        ] as const,
    );
    const input = new Set(edges.map(([a, b]) => `${a} ${b}`));
    const got = model(bend, edges, 8);
    assertEquals(
      [...got.edges].sort(),
      [...reference(edges)].sort(),
      `seed ${seed}: ${JSON.stringify(edges)}`,
    );
    // dedupe: rounds add each new edge once, never a copy
    assertEquals(
      got.listLength,
      edges.length + got.edges.size - input.size,
      `seed ${seed}: the model's list holds duplicates`,
    );
    if (got.edges.size > input.size) grew++;
    if ([...got.edges].some((e) => e.split(" ")[0] === e.split(" ")[1])) {
      cyclic++;
    }
  }
  console.log(`compared 500 graphs (${grew} grew, ${cyclic} with a cycle)`);
  assert(grew >= 200, `closing added edges in only ${grew} graphs: too easy`);
  assert(cyclic >= 50, `only ${cyclic} graphs had a cycle`);
});
