/**
 * The pilot's TypeScript reference (reasoner#39, Phase 1): a semi-naive
 * closure over integer triples for exactly six OWL 2 RL rules, so a Bend
 * implementation is timed against the same work, not the full ruleset.
 *
 * - cax-sco: (c1 subClassOf c2), (x type c1) -> (x type c2)
 * - scm-sco: subClassOf is transitive
 * - prp-dom: (p domain c), (x p y) -> (x type c)
 * - prp-rng: (p range c), (x p y) -> (y type c)
 * - prp-trp: (p type TransitiveProperty), (x p y), (y p z) -> (x p z)
 * - prp-inv1/2: (p1 inverseOf p2), (x p1 y) <-> (y p2 x)
 *
 * Every triple is indexed by predicate both ways (s -> o and o -> s), so each
 * rule premise is one lookup. A triple enters `next` only when it is new, and
 * each round fires every rule in which a `delta` triple can be a premise,
 * joined against the whole store.
 */
import { V } from "./encode.ts";

type Index = Map<number, Map<number, Set<number>>>;

const EMPTY: ReadonlySet<number> = new Set();

function put(index: Index, p: number, a: number, b: number): boolean {
  let byA = index.get(p);
  if (byA === undefined) index.set(p, byA = new Map());
  let bs = byA.get(a);
  if (bs === undefined) byA.set(a, bs = new Set());
  if (bs.has(b)) return false;
  bs.add(b);
  return true;
}

/** Store is the closure so far, indexed by predicate in both directions. */
class Store {
  readonly spo: Index = new Map();
  readonly pos: Index = new Map();
  next: number[] = [];
  size = 0;

  add(s: number, p: number, o: number): void {
    if (!put(this.spo, p, s, o)) return;
    put(this.pos, p, o, s);
    this.next.push(s, p, o);
    this.size++;
  }

  objects(p: number, s: number): ReadonlySet<number> {
    return this.spo.get(p)?.get(s) ?? EMPTY;
  }

  subjects(p: number, o: number): ReadonlySet<number> {
    return this.pos.get(p)?.get(o) ?? EMPTY;
  }

  /** pairs calls `f(x, y)` for every asserted or derived `(x p y)`. */
  pairs(p: number, f: (x: number, y: number) => void): void {
    for (const [x, ys] of this.spo.get(p) ?? []) for (const y of ys) f(x, y);
  }
}

/** schema fires the rules in which `(s p o)` is the schema premise. */
function schema(st: Store, s: number, p: number, o: number): void {
  if (p === V.subClassOf) {
    for (const x of st.subjects(V.type, s)) st.add(x, V.type, o); // cax-sco
    for (const c of st.subjects(V.subClassOf, s)) st.add(c, p, o); // scm-sco
    for (const c of st.objects(V.subClassOf, o)) st.add(s, p, c); // scm-sco
  } else if (p === V.domain) {
    st.pairs(s, (x) => st.add(x, V.type, o)); // prp-dom
  } else if (p === V.range) {
    st.pairs(s, (_, y) => st.add(y, V.type, o)); // prp-rng
  } else if (p === V.inverseOf) {
    st.pairs(s, (x, y) => st.add(y, o, x)); // prp-inv1
    st.pairs(o, (x, y) => st.add(y, s, x)); // prp-inv2
  } else if (p === V.type && o === V.transitive) {
    st.pairs(s, (x, y) => { // prp-trp
      for (const z of st.objects(s, y)) st.add(x, s, z);
    });
  }
}

/** instance fires the rules in which `(x p y)` is the data premise. */
function instance(st: Store, x: number, p: number, y: number): void {
  if (p === V.type) {
    for (const c of st.objects(V.subClassOf, y)) st.add(x, V.type, c); // cax-sco
  }
  for (const c of st.objects(V.domain, p)) st.add(x, V.type, c); // prp-dom
  for (const c of st.objects(V.range, p)) st.add(y, V.type, c); // prp-rng
  for (const q of st.objects(V.inverseOf, p)) st.add(y, q, x); // prp-inv1
  for (const q of st.subjects(V.inverseOf, p)) st.add(y, q, x); // prp-inv2
  if (st.subjects(V.type, V.transitive).size > 0) {
    if (st.objects(V.type, p).has(V.transitive)) { // prp-trp
      for (const z of st.objects(p, y)) st.add(x, p, z);
      for (const w of st.subjects(p, x)) st.add(w, p, y);
    }
  }
}

/** Closure is the result of {@link closure}. */
export interface Closure {
  /** triples is every asserted and derived triple, flat `[s, p, o, ...]`. */
  readonly triples: Uint32Array;
  readonly rounds: number;
}

/** closure computes the six-rule closure of flat `[s, p, o, ...]` triples. */
export function closure(input: Uint32Array): Closure {
  const st = new Store();
  for (let i = 0; i < input.length; i += 3) {
    st.add(input[i], input[i + 1], input[i + 2]);
  }
  let rounds = 0;
  while (st.next.length > 0) {
    const delta = st.next;
    st.next = [];
    rounds++;
    for (let i = 0; i < delta.length; i += 3) {
      schema(st, delta[i], delta[i + 1], delta[i + 2]);
      instance(st, delta[i], delta[i + 1], delta[i + 2]);
    }
  }
  const triples = new Uint32Array(st.size * 3);
  let n = 0;
  for (const [p, byS] of st.spo) {
    for (const [s, os] of byS) {
      for (const o of os) {
        triples[n++] = s;
        triples[n++] = p;
        triples[n++] = o;
      }
    }
  }
  return { triples, rounds };
}
