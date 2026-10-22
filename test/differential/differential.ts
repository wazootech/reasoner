// Differential oracle for Reasoner.extend(): a base graph plus a delta added
// incrementally must give the same closure and inconsistencies as the whole
// graph added up front. Seeded, so every failure is reproducible.
import type { Quad } from "@rdfjs/types";
import { dataFactory as df } from "@wazoo/sparql-engine/term";
import { Reasoner } from "@/mod.ts";

const E = "http://d.example/";
const OWL = "http://www.w3.org/2002/07/owl#";
const RDFS = "http://www.w3.org/2000/01/rdf-schema#";
const RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";

/** T3 is a plain [s, p, o] of short names, easy to print and shrink. */
export type T3 = readonly [string, string, string];

const INDIVIDUALS = ["i0", "i1", "i2", "i3", "i4"];
const CLASSES = ["C0", "C1", "C2"];
const PROPS = ["p0", "p1", "p2", "p3"];
const LITERALS = ['"1"', '"2"'];
const PROP_KINDS = [
  "FunctionalProperty",
  "InverseFunctionalProperty",
  "TransitiveProperty",
  "SymmetricProperty",
  "IrreflexiveProperty",
  "AsymmetricProperty",
];
const OWL_NAMES = ["sameAs", "differentFrom", "inverseOf", ...PROP_KINDS];
const RDFS_NAMES = ["subClassOf", "domain", "range", "subPropertyOf"];

/** prng is mulberry32, a tiny seeded generator. */
export function prng(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** generate builds a small random graph of 10 to 40 triples. */
export function generate(seed: number): T3[] {
  const rnd = prng(seed);
  const pick = <X>(xs: readonly X[]): X => xs[Math.floor(rnd() * xs.length)]!;
  const n = 10 + Math.floor(rnd() * 31);
  const out = new Map<string, T3>();
  while (out.size < n) {
    const r = rnd();
    let t: T3;
    if (r < 0.28) {
      const o = rnd() < 0.2 ? pick(LITERALS) : pick(INDIVIDUALS);
      t = [pick(INDIVIDUALS), pick(PROPS), o];
    } else if (r < 0.38) t = [pick(INDIVIDUALS), "a", pick(CLASSES)];
    else if (r < 0.52) t = [pick(PROPS), "a", pick(PROP_KINDS)];
    else if (r < 0.64) {
      const o = rnd() < 0.3 ? pick(LITERALS) : pick(INDIVIDUALS);
      t = [pick(INDIVIDUALS), "sameAs", o];
    } else if (r < 0.70) {
      t = [pick(INDIVIDUALS), "differentFrom", pick(INDIVIDUALS)];
    } else if (r < 0.77) t = [pick(CLASSES), "subClassOf", pick(CLASSES)];
    else if (r < 0.83) t = [pick(PROPS), "domain", pick(CLASSES)];
    else if (r < 0.89) t = [pick(PROPS), "range", pick(CLASSES)];
    else if (r < 0.95) t = [pick(PROPS), "inverseOf", pick(PROPS)];
    else t = [pick(PROPS), "subPropertyOf", pick(PROPS)];
    out.set(t.join(" "), t);
  }
  return [...out.values()];
}

function term(s: string) {
  if (s.startsWith('"')) return df.literal(s.slice(1, -1));
  if (s === "a") return df.namedNode(RDF_TYPE);
  if (OWL_NAMES.includes(s)) return df.namedNode(OWL + s);
  if (RDFS_NAMES.includes(s)) return df.namedNode(RDFS + s);
  return df.namedNode(E + s);
}

function quad([s, p, o]: T3): Quad {
  return df.quad(term(s), term(p), term(o));
}

function key(q: Quad): string {
  const t = (x: Quad["subject"] | Quad["object"]) =>
    x.termType === "Literal"
      ? `"${x.value}"^^${x.datatype.value}@${x.language}`
      : x.termType + ":" + x.value;
  return `${t(q.subject)} ${q.predicate.value} ${t(q.object)}`;
}

export interface Outcome {
  closure: Set<string>;
  inconsistencies: Set<string>;
}

function outcome(r: Reasoner): Outcome {
  return {
    closure: new Set([...r.closure("complete")].map(key)),
    // Reported terms are the class representatives, which depend on merge
    // order, so only the violated rule is compared.
    inconsistencies: new Set(r.inconsistencies().map((i) => i.rule)),
  };
}

export function full(base: readonly T3[], delta: readonly T3[]): Outcome {
  const r = new Reasoner();
  r.add([...base, ...delta].map(quad));
  r.run();
  return outcome(r);
}

export function incremental(
  base: readonly T3[],
  delta: readonly T3[],
): Outcome {
  const r = new Reasoner();
  r.add(base.map(quad));
  r.run();
  r.extend(delta.map(quad));
  return outcome(r);
}

export interface Diff {
  /** missing is in the full run but not in the incremental one. */
  missing: string[];
  /** extra is in the incremental run but not in the full one. */
  extra: string[];
  missingInconsistencies: string[];
  extraInconsistencies: string[];
}

function minus(a: Set<string>, b: Set<string>): string[] {
  return [...a].filter((x) => !b.has(x)).sort();
}

export function diff(base: readonly T3[], delta: readonly T3[]): Diff | null {
  const f = full(base, delta);
  const i = incremental(base, delta);
  const d = {
    missing: minus(f.closure, i.closure),
    extra: minus(i.closure, f.closure),
    missingInconsistencies: minus(f.inconsistencies, i.inconsistencies),
    extraInconsistencies: minus(i.inconsistencies, f.inconsistencies),
  };
  return Object.values(d).every((x) => x.length === 0) ? null : d;
}

const local = (s: string) => s.replace(/^.*[#/]/, "");

/**
 * classify names a failure by the predicates of the differing triples and the
 * rules of the differing inconsistencies, so equal causes share one class.
 */
export function classify(d: Diff): string {
  const preds = (xs: string[]) =>
    [...new Set(xs.map((x) => local(x.split(" ")[1]!)))].sort().join(",");
  const rules = (xs: string[]) =>
    [...new Set(xs.map((x) => local(x)))].sort().join(",");
  return [
    d.missing.length ? `missing[${preds(d.missing)}]` : "",
    d.extra.length ? `extra[${preds(d.extra)}]` : "",
    d.missingInconsistencies.length
      ? `missing-inconsistency[${rules(d.missingInconsistencies)}]`
      : "",
    d.extraInconsistencies.length
      ? `extra-inconsistency[${rules(d.extraInconsistencies)}]`
      : "",
  ].filter(Boolean).join(" ");
}

/**
 * shrink greedily removes triples from base and delta while the failure
 * class stays the same, so the repro is small and keeps its meaning.
 */
export function shrink(
  base: T3[],
  delta: T3[],
  cls: string,
): { base: T3[]; delta: T3[] } {
  const still = (b: T3[], d: T3[]) => {
    const x = diff(b, d);
    return x !== null && classify(x) === cls;
  };
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < base.length; i++) {
      const b = base.filter((_, j) => j !== i);
      if (still(b, delta)) {
        base = b;
        changed = true;
        i--;
      }
    }
    for (let i = 0; i < delta.length; i++) {
      const d = delta.filter((_, j) => j !== i);
      if (still(base, d)) {
        delta = d;
        changed = true;
        i--;
      }
    }
  }
  return { base, delta };
}

export interface Failure {
  seed: number;
  cls: string;
  base: T3[];
  delta: T3[];
  diff: Diff;
}

/** runSeed splits the seed's graph at a seeded random point and compares. */
export function runSeed(seed: number): Failure | null {
  const triples = generate(seed);
  const rnd = prng(seed ^ 0x9E3779B9);
  const cut = 1 + Math.floor(rnd() * (triples.length - 1));
  const base = triples.slice(0, cut);
  const delta = triples.slice(cut);
  const d = diff(base, delta);
  if (d === null) return null;
  const cls = classify(d);
  const small = shrink(base, delta, cls);
  return { seed, cls, ...small, diff: diff(small.base, small.delta)! };
}

export const fmt = (ts: readonly T3[]) =>
  ts.map((t) => t.join(" ")).join(" .\n") + " .";
