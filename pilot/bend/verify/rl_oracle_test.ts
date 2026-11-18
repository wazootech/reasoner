/**
 * Differential test (reasoner#45): the six-rule Bend model in `rl.bend`, whose
 * laws are proved in RL_PROOF.bend, against the pilot's TypeScript reference
 * closure on random graphs that exercise every rule.
 *
 * Input crosses the JS/Bend boundary as the flat `Uint32Array` of
 * `[s, p, o, ...]` that `encode.ts` produces, and the result comes back the
 * same way. Needs `bend` on the PATH and is skipped without it.
 *
 *     deno test --allow-read --allow-write --allow-run --allow-env \
 *       pilot/bend/verify/rl_oracle_test.ts
 */
import { assert, assertEquals } from "@std/assert";
import { V } from "../encode.ts";
import { closure } from "../reference.ts";
import { type Bend, hasBend, load, random } from "./bend_util.ts";

/** toBend turns flat triples into the model's `Ts` list. */
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

function keys(flat: Uint32Array): Set<string> {
  const out = new Set<string>();
  for (let i = 0; i < flat.length; i += 3) {
    out.add(`${flat[i]} ${flat[i + 1]} ${flat[i + 2]}`);
  }
  return out;
}

/** model runs rounds until the proved stop test passes, up to `limit`. */
function model(bend: Bend, input: Uint32Array, limit: number): Uint32Array {
  const start = toBend(input);
  for (let rounds = 0; rounds <= limit; rounds++) {
    const r = bend.iter(rounds, start);
    if (bend.subset(bend.step(r), r) === true) return fromBend(r);
  }
  throw new Error(`no fixpoint within ${limit} rounds`);
}

const CLASSES = 5, PROPS = 3, THINGS = 5;
const cls = (r: () => number) => 10 + Math.floor(r() * CLASSES);
const prop = (r: () => number) => 20 + Math.floor(r() * PROPS);
const thing = (r: () => number) => 30 + Math.floor(r() * THINGS);

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

Deno.test({
  name: "Bend six-rule model matches the TypeScript reference on random graphs",
  ignore: !hasBend(),
  fn: async () => {
    const bend = await load("rl.bend");
    let grew = 0;
    const fired = new Set<string>();
    for (let seed = 1; seed <= 400; seed++) {
      const input = graph(random(seed));
      const got = keys(model(bend, input, 10));
      const want = keys(closure(input).triples);
      assertEquals([...got].sort(), [...want].sort(), `seed ${seed}`);
      // no duplicates: the list is exactly the set
      assertEquals(
        fromBend(bend.iter(0, toBend(input))).length,
        input.length,
      );
      if (got.size > keys(input).size) grew++;
      for (const t of got) if (!keys(input).has(t)) fired.add(t.split(" ")[1]);
    }
    console.log(
      `compared 400 graphs (${grew} grew); derived predicates seen: ${
        [...fired].sort()
      }`,
    );
    assert(grew >= 200, `closing added triples in only ${grew} graphs`);
    // type (0), subClassOf (1), and at least one data predicate (20+) derived
    assert(
      fired.has("0") && fired.has("1"),
      "cax/prp-dom/rng and scm-sco never fired",
    );
    assert([...fired].some((p) => Number(p) >= 20), "prp-inv/trp never fired");
  },
});
