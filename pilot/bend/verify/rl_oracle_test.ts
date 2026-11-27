/**
 * Differential test (reasoner#45): the six-rule Bend model in `rl.bend`, whose
 * laws are proved in RL_PROOF.bend, against the pilot's TypeScript reference
 * closure on random graphs that exercise every rule.
 *
 * Input crosses the JS/Bend boundary as the flat `Uint32Array` of
 * `[s, p, o, ...]` that `encode.ts` produces, and the result comes back the
 * same way. Needs `bend` on the PATH and is skipped without it.
 *
 *     bun test pilot/bend/verify/rl_oracle_test.ts
 */
import { test } from "node:test";
import { assert, assertEquals } from "../../../test/asserts.ts";
import { V } from "../encode.ts";
import { closure } from "../reference.ts";
import { Reasoner } from "@/mod.ts";
import { generate } from "../../../bench/scaling.ts";
import { encode } from "../encode.ts";
import {
  closeModel,
  closeSemi,
  fromBend,
  hasBend,
  load,
  random,
  toBend,
} from "./bend_util.ts";

function keys(flat: Uint32Array): Set<string> {
  const out = new Set<string>();
  for (let i = 0; i < flat.length; i += 3) {
    out.add(`${flat[i]} ${flat[i + 1]} ${flat[i + 2]}`);
  }
  return out;
}

const CLASSES = 5,
  PROPS = 3,
  THINGS = 5;
// A class is sometimes TransitiveProperty itself, so (p domain/range/sub TransitiveProperty)
// can derive `(p type TransitiveProperty)` in a later round, not just assert it.
const cls = (r: () => number) =>
  r() < 0.12 ? V.transitive : 10 + Math.floor(r() * CLASSES);
const prop = (r: () => number) => 20 + Math.floor(r() * PROPS);
// Things are sometimes properties, so a property can be the subject of a type triple.
const thing = (r: () => number) =>
  r() < 0.2 ? prop(r) : 30 + Math.floor(r() * THINGS);

/** graph draws schema, type and data triples so every rule can fire. */
function graph(r: () => number): Uint32Array {
  const flat: number[] = [];
  const add = (s: number, p: number, o: number) => flat.push(s, p, o);
  const n = 3 + Math.floor(r() * 12);
  for (let i = 0; i < n; i++) {
    const k = Math.floor(r() * 8);
    if (k === 0) add(cls(r), V.subClassOf, cls(r));
    else if (k === 1) add(thing(r), V.type, cls(r));
    else if (k === 2) add(prop(r), V.domain, cls(r));
    else if (k === 3) add(prop(r), V.range, cls(r));
    else if (k === 4) add(prop(r), V.inverseOf, prop(r));
    else if (k === 5) add(prop(r), V.type, V.transitive);
    else add(thing(r), prop(r), thing(r));
  }
  return Uint32Array.from(flat);
}

test(
  "Bend six-rule model matches the TypeScript reference on random graphs",
  {
    skip: !hasBend(),
  },
  async () => {
    const bend = await load("rl.bend");
    let grew = 0;
    const fired = new Set<string>();
    for (let seed = 1; seed <= 400; seed++) {
      const input = graph(random(seed));
      const got = keys(closeModel(bend, input, 10));
      const want = keys(closure(input).triples);
      assertEquals([...got].sort(), [...want].sort(), `seed ${seed}`);
      // no duplicates: the list is exactly the set
      assertEquals(fromBend(bend.iter(0, toBend(input))).length, input.length);
      if (got.size > keys(input).size) grew++;
      for (const t of got) if (!keys(input).has(t)) fired.add(t.split(" ")[1]);
    }
    console.log(
      `compared 400 graphs (${grew} grew); derived predicates seen: ${[
        ...fired,
      ].sort()}`,
    );
    assert(grew >= 200, `closing added triples in only ${grew} graphs`);
    // type (0), subClassOf (1), and at least one data predicate (20+) derived
    assert(
      fired.has("0") && fired.has("1"),
      "cax/prp-dom/rng and scm-sco never fired",
    );
    assert(
      [...fired].some((p) => Number(p) >= 20),
      "prp-inv/trp never fired",
    );
  },
);

test(
  "Bend model equals the reference and is a subset of Reasoner on plain",
  {
    skip: !hasBend(),
  },
  async () => {
    const bend = await load("rl.bend");
    // The model is quadratic per round, so these sizes take seconds, not 1e4.
    for (const size of [30, 60]) {
      const quads = generate(size, "plain");
      const { triples, dictionary } = encode(quads);
      const got = keys(closeModel(bend, triples, 10));
      assertEquals([...got].sort(), [...keys(closure(triples).triples)].sort());
      const reasoner = new Reasoner();
      reasoner.add(quads);
      reasoner.run();
      const theirs = new Set<string>();
      for (const q of reasoner.closure("complete")) {
        theirs.add(
          [q.subject, q.predicate, q.object]
            .map((t) => dictionary.lookup(t))
            .join(" "),
        );
      }
      const extra = [...got].filter((t) => !theirs.has(t));
      assertEquals(extra, [], "the model derives a triple Reasoner does not");
    }
  },
);

test(
  "Bend semi-naive loop equals the naive loop and the reference",
  {
    skip: !hasBend(),
  },
  async () => {
    const bend = await load("rl.bend");
    let late = 0;
    for (let seed = 1; seed <= 600; seed++) {
      const input = graph(random(seed));
      const naive = keys(closeModel(bend, input, 10));
      assertEquals(
        [...keys(closeSemi(bend, input, 10))].sort(),
        [...naive].sort(),
        `seed ${seed}`,
      );
      assertEquals([...naive].sort(), [...keys(closure(input).triples)].sort());
      // a transitive declaration that was derived, not asserted
      const asserted = keys(input);
      const declared = (t: string) => {
        const [, p, o] = t.split(" ");
        return p === String(V.type) && o === String(V.transitive);
      };
      if ([...naive].some((t) => declared(t) && !asserted.has(t))) late++;
    }
    console.log(
      `semi-naive = naive = reference on 600 graphs (${late} derive a new transitive declaration)`,
    );
    assert(late >= 20, `only ${late} graphs derived a transitive declaration`);
  },
);
