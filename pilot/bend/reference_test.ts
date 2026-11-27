/**
 * Checks the pilot reference two independent ways (reasoner#39, Phase 1):
 * against a brute-force pairwise fixpoint on random graphs, and as a subset of
 * the full Reasoner's closure on the `plain` bench profile, with every triple
 * the reference leaves out attributed to a rule outside its six.
 *
 *     deno test --allow-read pilot/bend/reference_test.ts
 */
import { test } from "node:test";
import { assertEquals } from "../../test/asserts.ts";
import { Reasoner } from "@/mod.ts";
import { generate } from "../../bench/scaling.ts";
import { encode, V } from "./encode.ts";
import { closure } from "./reference.ts";
import { closeModel, hasBend, load } from "./verify/bend_util.ts";

type T = readonly [number, number, number];

function keys(flat: Uint32Array): Set<string> {
  const out = new Set<string>();
  for (let i = 0; i < flat.length; i += 3) {
    out.add(`${flat[i]} ${flat[i + 1]} ${flat[i + 2]}`);
  }
  return out;
}

/** derive returns what the six rules derive from one pair of triples. */
function derive(a: T, b: T, transitive: Set<number>): T[] {
  const out: T[] = [];
  const [as, ap, ao] = a, [bs, bp, bo] = b;
  if (ap === V.subClassOf && bp === V.type && bo === as) {
    out.push([bs, V.type, ao]);
  }
  if (ap === V.subClassOf && bp === V.subClassOf && bs === ao) {
    out.push([as, ap, bo]);
  }
  if (ap === V.domain && bp === as) out.push([bs, V.type, ao]);
  if (ap === V.range && bp === as) out.push([bo, V.type, ao]);
  if (ap === V.inverseOf && bp === as) out.push([bo, ao, bs]);
  if (ap === V.inverseOf && bp === ao) out.push([bo, as, bs]);
  if (transitive.has(ap) && bp === ap && bs === ao) out.push([as, ap, bo]);
  return out;
}

/** bruteForce applies every rule to every pair until nothing is new. */
function bruteForce(input: Uint32Array): Set<string> {
  const all: T[] = [];
  const seen = new Set<string>();
  const add = (t: T) => {
    const k = t.join(" ");
    if (seen.has(k)) return;
    seen.add(k);
    all.push(t);
  };
  for (let i = 0; i < input.length; i += 3) {
    add([input[i], input[i + 1], input[i + 2]]);
  }
  for (let before = -1; before !== all.length;) {
    before = all.length;
    const transitive = new Set(
      all.filter(([, p, o]) => p === V.type && o === V.transitive).map(([s]) =>
        s
      ),
    );
    for (const a of all.slice()) {
      for (const b of all.slice()) derive(a, b, transitive).forEach(add);
    }
  }
  return seen;
}

/** randomGraph uses few terms and mostly vocabulary predicates, so rules interact. */
function randomGraph(seed: number): Uint32Array {
  let x = seed;
  const next = (n: number) =>
    (x = (Math.imul(x, 1664525) + 1013904223) >>> 0) % n;
  const out: number[] = [];
  for (let i = 0; i < 12 + next(20); i++) {
    const p = next(3) === 0 ? 6 + next(4) : next(5);
    out.push(6 + next(8), p, next(10) === 0 ? V.transitive : 6 + next(8));
  }
  return new Uint32Array(out);
}

test("reference equals brute force on 500 random graphs", () => {
  for (let seed = 1; seed <= 500; seed++) {
    const input = randomGraph(seed);
    assertEquals(
      keys(closure(input).triples),
      bruteForce(input),
      `seed ${seed}`,
    );
  }
});

test(
  "Bend model equals brute force on 40 random graphs",
  { skip: !hasBend() },
  async () => {
    // The Bend model's laws are proved in verify/RL_PROOF.bend; this ties the
    // proved model to the independent brute force, not just to `closure`.
    const bend = await load("rl.bend");
    for (let seed = 1; seed <= 40; seed++) {
      const input = randomGraph(seed);
      assertEquals(
        keys(closeModel(bend, input, 10)),
        bruteForce(input),
        `seed ${seed}`,
      );
    }
  },
);

/** leftOut counts, by predicate (and class for rdf:type), what Reasoner adds. */
function leftOut(size: number): Map<string, number> {
  const quads = generate(size, "plain");
  const { triples, dictionary } = encode(quads);
  const ours = keys(closure(triples).triples);
  const reasoner = new Reasoner();
  reasoner.add(quads);
  reasoner.run();
  const missing = new Map<string, number>();
  const local = (t: { termType: string; value: string }) =>
    t.termType === "NamedNode" ? t.value.replace(/^.*[#/]/, "") : t.termType;
  for (const q of reasoner.closure("complete")) {
    const ids = [q.subject, q.predicate, q.object].map((t) =>
      dictionary.lookup(t)
    );
    if (ours.delete(ids.join(" "))) continue;
    const p = local(q.predicate);
    const label = p === "type" ? `type ${local(q.object)}` : p;
    missing.set(label, (missing.get(label) ?? 0) + 1);
  }
  assertEquals([...ours], [], "reference derives a triple Reasoner does not");
  return missing;
}

/** INSTANCE are the labels that scale with the data, each from another rule. */
const INSTANCE = {
  "knows": "prp-symp",
  "type string": "dt-type2",
  "type Literal": "dt-type2",
};

test("reference is a subset of Reasoner on plain, gaps attributed", () => {
  const [small, large] = [leftOut(1e3), leftOut(1e4)];
  for (const [size, missing] of [[1e3, small], [1e4, large]] as const) {
    // One literal name per person; one symmetric knows per person, less ties.
    assertEquals(missing.get("type string"), size / 5);
    assertEquals(missing.get("type Literal"), size / 5);
    const knows = missing.get("knows") ?? 0;
    assertEquals(knows > size / 5 - 10 && knows <= size / 5, true, `${knows}`);
  }
  // The rest is schema-level (axiomatic triples and scm-*): it must not grow
  // with the data, or the reference is missing an instance-level derivation.
  const schema = (m: Map<string, number>) =>
    [...m].filter(([label]) => !(label in INSTANCE)).sort();
  assertEquals(schema(large), schema(small));
});
