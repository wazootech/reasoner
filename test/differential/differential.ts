// Differential oracles for Reasoner.extend() and Reasoner.retract().
//
// - extend: a base graph plus a delta added incrementally must give the same
//   closure and inconsistencies as the whole graph added up front.
// - retract: the whole graph with the delta retracted must equal a fresh run on
//   the base alone, and the triples retract reports must be exactly the ones
//   that fresh run lost. "retract-instance" retracts only triples about
//   individuals, the case retract recomputes locally; "retract-full" forces
//   the whole-closure fallback.
// - union-extend, union-retract: the same, with every triple asserted in one or
//   two of four graphs and a Reasoner in "union" mode; the closure must equal
//   the default-graph run, and every quad must be in the default graph.
// - graphs-extend, graphs-retract, graphs-retract-partial: the same with a
//   per-graph Reasoner, against an independent oracle built from default-graph
//   Reasoners: a triple is listed in each graph whose own closure entails it,
//   in the default graph when an axiom, and in the derived graph when only the
//   union entails it. The retract-partial mode retracts one copy of a triple
//   asserted in two graphs, which must stay asserted in the other.
//
// Seeded, so every failure is reproducible.
import type { Quad } from "@rdfjs/types";
import { dataFactory as df } from "@wazoo/sparql-engine/term";
import { Reasoner } from "@/mod.ts";
import { isSkolemTerm } from "@/owl2rl/rules.ts";

const E = "http://d.example/";
const OWL = "http://www.w3.org/2002/07/owl#";
const XSD = "http://www.w3.org/2001/XMLSchema#";
const RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS = "http://www.w3.org/2000/01/rdf-schema#";
const RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";

/** T3 is a plain [s, p, o] of short names, easy to print and shrink. */
export type T3 = readonly [string, string, string];

const INDIVIDUALS = ["i0", "i1", "i2", "i3", "i4", "_:b0", "_:b1"];
const CLASSES = ["C0", "C1", "C2"];
const PROPS = ["p0", "p1", "p2", "p3"];
// Plain, typed (including numerically equal ones), and language-tagged.
const LITERALS = [
  '"1"',
  '"2"',
  '"1"^^xsd:integer',
  '"01"^^xsd:integer',
  '"1"^^xsd:decimal',
  '"1.0"^^xsd:decimal',
  '"1"^^xsd:int',
  '"2"^^xsd:decimal',
  '"2.00"^^xsd:decimal',
  '"1.5"^^xsd:double',
  '"1.50"^^xsd:double',
  '"1.5"^^xsd:float',
  '"true"^^xsd:boolean',
  '"1"^^xsd:boolean',
  '"false"^^xsd:boolean',
  '"a"@en',
  '"a"@fr',
];
const PROP_KINDS = [
  "FunctionalProperty",
  "InverseFunctionalProperty",
  "TransitiveProperty",
  "SymmetricProperty",
  "IrreflexiveProperty",
  "AsymmetricProperty",
];
const OWL_NAMES = [
  "sameAs",
  "differentFrom",
  "inverseOf",
  "equivalentClass",
  "hasKey",
  "someValuesFrom",
  "allValuesFrom",
  "onProperty",
  "onClass",
  "maxCardinality",
  "maxQualifiedCardinality",
  "intersectionOf",
  "unionOf",
  "propertyChainAxiom",
  ...PROP_KINDS,
];
const RDF_NAMES = ["first", "rest", "nil"];
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
  // An individual is occasionally a class or a property (punning), so schema
  // triples and instance triples share terms.
  const ind = () =>
    rnd() < 0.1 ? pick([...CLASSES, ...PROPS]) : pick(INDIVIDUALS);
  const out = new Map<string, T3>();
  let fresh = 0;
  const add = (...ts: T3[]) => ts.forEach((t) => out.set(t.join(" "), t));
  /** list adds an RDF list of the members and returns its head. */
  const list = (members: string[]): string => {
    const id = fresh++;
    members.forEach((m, i) => {
      add([`_:l${id}_${i}`, "first", m]);
      add([
        `_:l${id}_${i}`,
        "rest",
        i + 1 < members.length ? `_:l${id}_${i + 1}` : "nil",
      ]);
    });
    return `_:l${id}_0`;
  };
  /** structure adds list-based axioms and restrictions. */
  const structure = () => {
    const k = Math.floor(rnd() * 8);
    const c = pick(CLASSES);
    const p = pick(PROPS);
    const restriction = () => `_:r${fresh++}`;
    if (k === 0) {
      add([
        c,
        "hasKey",
        list([p, pick(PROPS)].slice(0, 1 + Math.floor(rnd() * 2))),
      ]);
    } else if (k === 1) {
      add([c, "intersectionOf", list([pick(CLASSES), pick(CLASSES)])]);
    } else if (k === 2) {
      add([c, "unionOf", list([pick(CLASSES), pick(CLASSES)])]);
    } else if (k === 3) {
      add([
        p,
        "propertyChainAxiom",
        list([pick(PROPS), pick(PROPS), ...(rnd() < 0.3 ? [pick(PROPS)] : [])]),
      ]);
    } else {
      const r = restriction();
      add([r, "onProperty", p]);
      const dir = rnd();
      if (k === 4) {
        add([r, "someValuesFrom", pick(CLASSES)]);
        add(dir < 0.5 ? [r, "subClassOf", c] : [c, "subClassOf", r]);
      } else if (k === 5) {
        add([r, "allValuesFrom", pick(CLASSES)]);
        add(dir < 0.5 ? [c, "subClassOf", r] : [r, "subClassOf", c]);
      } else if (k === 6) {
        add([r, "maxCardinality", '"1"^^xsd:nonNegativeInteger']);
        add([pick(INDIVIDUALS), "a", r]);
      } else {
        add([r, "maxQualifiedCardinality", '"1"^^xsd:nonNegativeInteger']);
        add([r, "onClass", pick(CLASSES)]);
        add([pick(INDIVIDUALS), "a", r]);
      }
    }
  };
  while (out.size < n) {
    const r = rnd();
    let t: T3;
    if (r < 0.1) {
      structure();
      continue;
    }
    if (r < 0.3) {
      const o = rnd() < 0.2 ? pick(LITERALS) : ind();
      t = [ind(), pick(PROPS), o];
    } else if (r < 0.38) t = [ind(), "a", pick(CLASSES)];
    else if (r < 0.52) t = [pick(PROPS), "a", pick(PROP_KINDS)];
    else if (r < 0.64) {
      const o = rnd() < 0.3 ? pick(LITERALS) : ind();
      t = [ind(), "sameAs", o];
    } else if (r < 0.70) {
      t = [ind(), "differentFrom", ind()];
    } else if (r < 0.77) t = [pick(CLASSES), "subClassOf", pick(CLASSES)];
    else if (r < 0.83) t = [pick(PROPS), "domain", pick(CLASSES)];
    else if (r < 0.89) t = [pick(PROPS), "range", pick(CLASSES)];
    else if (r < 0.95) t = [pick(PROPS), "inverseOf", pick(PROPS)];
    else t = [pick(PROPS), "subPropertyOf", pick(PROPS)];
    add(t);
  }
  return [...out.values()];
}

function term(s: string) {
  if (s.startsWith('"')) {
    const m = /^"(.*)"(?:\^\^xsd:(\w+)|@(\w+))?$/.exec(s)!;
    if (m[3]) return df.literal(m[1]!, m[3]);
    if (m[2]) return df.literal(m[1]!, df.namedNode(XSD + m[2]));
    return df.literal(m[1]!);
  }
  if (s.startsWith("_:")) return df.blankNode(s.slice(2));
  if (RDF_NAMES.includes(s)) return df.namedNode(RDF + s);
  if (s === "a") return df.namedNode(RDF_TYPE);
  if (OWL_NAMES.includes(s)) return df.namedNode(OWL + s);
  if (RDFS_NAMES.includes(s)) return df.namedNode(RDFS + s);
  return df.namedNode(E + s);
}

function quadIn([s, p, o]: T3, graph?: string): Quad {
  return df.quad(
    term(s),
    term(p),
    term(o),
    graph === undefined || graph === "default"
      ? df.defaultGraph()
      : df.namedNode(E + graph),
  );
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

/**
 * isSkolem is `true` for a triple naming a complement-class skolem. The engine
 * mints those for its own bookkeeping (the "application" view hides them), and
 * whether a given one exists depends on the order rules fired in, so they are
 * not compared; the inconsistencies they lead to are.
 */
function isSkolem(q: Quad): boolean {
  return [q.subject, q.predicate, q.object].some(isSkolemTerm);
}

function outcome(r: Reasoner): Outcome {
  return {
    closure: new Set(
      [...r.closure("complete")].filter((q) => !isSkolem(q)).map(key),
    ),
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

export type Mode =
  | "extend"
  | "retract"
  | "retract-instance"
  | "retract-full"
  | "union-extend"
  | "union-retract"
  | "graphs-extend"
  | "graphs-retract"
  | "graphs-retract-partial";
export const MODES: readonly Mode[] = [
  "extend",
  "retract",
  "retract-instance",
  "retract-full",
  "union-extend",
  "union-retract",
  "graphs-extend",
  "graphs-retract",
  "graphs-retract-partial",
];

/** GQ is a triple asserted in a named graph ("default" is the default one). */
type GQ = readonly [T3, string];
const GRAPHS = ["default", "g1", "g2", "g3"];

/**
 * placements puts each triple in one graph, and some in a second one, both
 * chosen by a hash of the triple so that shrinking a repro keeps them.
 */
function placements(ts: readonly T3[]): GQ[] {
  const out: GQ[] = [];
  for (const t of ts) {
    let h = 2166136261;
    for (const c of t.join(" ")) h = Math.imul(h ^ c.charCodeAt(0), 16777619);
    h >>>= 0;
    const first = h % GRAPHS.length;
    out.push([t, GRAPHS[first]!]);
    if ((h >>> 8) % 4 === 0) {
      out.push([t, GRAPHS[(first + 1 + ((h >>> 12) % 3)) % GRAPHS.length]!]);
    }
  }
  return out;
}

const quad = (t: T3) => quadIn(t);
const gquad = ([t, g]: GQ) => quadIn(t, g);
const DERIVED = "https://wazoo.dev/ns/reasoner#derived";
function nameOf(graph: Quad["graph"]): string {
  if (graph.termType === "DefaultGraph") return "default";
  return graph.value === DERIVED ? "derived" : graph.value.replace(E, "");
}
const gkey = (q: Quad) => `${nameOf(q.graph)}|${key(q)}`;

/** graphOutcome reads a per-graph reasoner; every listed quad must be had. */
function graphOutcome(r: Reasoner): Outcome {
  const closure = new Set<string>();
  for (const q of r.closure("complete")) {
    if (isSkolem(q)) continue;
    const k = gkey(q);
    const had = r.has(q.subject, q.predicate, q.object, q.graph);
    closure.add(had ? k : `!has ${k}`);
  }
  const inconsistencies = new Set(
    r.inconsistencies().map((i) =>
      `${nameOf(i.graph as Quad["graph"])}|${i.rule}`
    ),
  );
  return { closure, inconsistencies };
}

/** Plain is what the oracle keeps of a default-graph run. */
interface Plain {
  closure: Set<string>;
  rules: string[];
}
const plainCache = new Map<string, Plain>();

/**
 * plainRun is the default-graph closure of triples, the oracle's building
 * block. Runs repeat across a seed's oracle calls, so they are memoized.
 */
function plainRun(ts: readonly T3[]): Plain {
  const id = ts.map((t) => t.join(" ")).sort().join("|");
  let plain = plainCache.get(id);
  if (plain === undefined) {
    const r = new Reasoner();
    r.add(ts.map((t) => quad(t)));
    r.run();
    plain = {
      closure: new Set(
        [...r.closure("complete")].filter((q) => !isSkolem(q)).map(key),
      ),
      rules: r.inconsistencies().map((i) => i.rule),
    };
    if (plainCache.size > 4000) plainCache.clear();
    plainCache.set(id, plain);
  }
  return plain;
}

/**
 * oracle lists what a per-graph reasoner must give for `gqs`, from plain
 * default-graph runs only: a triple is in each graph that asserts it or whose
 * closure entails it, in the default graph when it is an axiom, and in the
 * derived graph when only the union entails it.
 */
function oracle(gqs: readonly GQ[]): Outcome {
  const byGraph = new Map<string, T3[]>();
  for (const [t, g] of gqs) byGraph.set(g, [...(byGraph.get(g) ?? []), t]);
  const axioms = plainRun([]).closure;
  const union = plainRun(gqs.map(([t]) => t));
  const alone = new Map<string, Set<string>>();
  const asserted = new Map<string, Set<string>>();
  const inconsistencies = new Set<string>();
  const ruled = new Set<string>();
  for (const [g, ts] of byGraph) {
    const r = plainRun(ts);
    alone.set(g, r.closure);
    asserted.set(g, new Set(ts.map((t) => key(quad(t)))));
    for (const rule of r.rules) {
      inconsistencies.add(`${g}|${rule}`);
      ruled.add(rule);
    }
  }
  for (const rule of union.rules) {
    if (!ruled.has(rule)) inconsistencies.add(`derived|${rule}`);
  }
  const closure = new Set<string>();
  for (const k of union.closure) {
    const labels = new Set<string>();
    const axiom = axioms.has(k);
    if (axiom) labels.add("default");
    for (const g of byGraph.keys()) {
      if (asserted.get(g)!.has(k) || (alone.get(g)!.has(k) && !axiom)) {
        labels.add(g);
      }
    }
    if (labels.size === 0) labels.add("derived");
    for (const g of labels) closure.add(`${g}|${k}`);
  }
  return { closure, inconsistencies };
}

function plainOutcome(ts: readonly T3[]): Outcome {
  const p = plainRun(ts);
  return { closure: p.closure, inconsistencies: new Set(p.rules) };
}

/** graphDiff compares a graph-mode run against its oracle. */
function graphDiff(
  base: readonly T3[],
  delta: readonly T3[],
  mode: Mode,
): Diff {
  const union = mode.startsWith("union");
  const kind = mode.replace(/^(union|graphs)-/, "");
  const baseQ = placements(base);
  const deltaQ = placements(delta);
  const r = new Reasoner({ graphs: union ? "union" : "per-graph" });
  /** read is the reasoner's outcome; union quads must all be default-graph. */
  const read = (): Outcome => {
    if (!union) return graphOutcome(r);
    const o = outcome(r);
    for (const q of r.closure("complete")) {
      if (q.graph.termType !== "DefaultGraph") o.closure.add(`graph ${key(q)}`);
    }
    return o;
  };
  /** want is the oracle: plain runs for union, the labelled oracle otherwise. */
  const want = (gqs: readonly GQ[]): Outcome =>
    union ? plainOutcome(gqs.map(([t]) => t)) : oracle(gqs);
  const listed = (q: Quad) => union ? key(q) : gkey(q);
  const everything = [...baseQ, ...deltaQ];
  let expected: Outcome;
  let reportedQuads: Quad[];
  let truth: string[];
  if (kind === "extend") {
    r.add(baseQ.map(gquad));
    r.run();
    reportedQuads = r.extend(deltaQ.map(gquad), "complete");
    expected = want(everything);
    truth = minus(expected.closure, want(baseQ).closure);
  } else {
    r.add(everything.map(gquad));
    r.run();
    // The partial mode retracts one copy of each triple; the rest stay.
    const gone = kind === "retract"
      ? deltaQ
      : deltaQ.filter(([t, g]) => g === deltaQ.find(([u]) => u === t)![1]);
    reportedQuads = r.retract(gone.map(gquad), "complete");
    const goneIds = new Set(gone.map(([t, g]) => `${g}|${t.join(" ")}`));
    expected = want(
      everything.filter(([t, g]) => !goneIds.has(`${g}|${t.join(" ")}`)),
    );
    truth = minus(want(everything).closure, expected.closure);
  }
  const got = read();
  const reported = new Set(
    reportedQuads.filter((q) => !isSkolem(q)).map(listed),
  );
  return {
    missing: minus(expected.closure, got.closure),
    extra: minus(got.closure, expected.closure),
    missingInconsistencies: minus(
      expected.inconsistencies,
      got.inconsistencies,
    ),
    extraInconsistencies: minus(got.inconsistencies, expected.inconsistencies),
    wrongRemoved: [
      ...minus(new Set(truth), reported),
      ...minus(reported, new Set(truth)),
    ],
  };
}

/** isInstance mirrors which triples retract recomputes locally. */
export function isInstance([, p, o]: T3): boolean {
  if (PROPS.includes(p)) return true;
  if (p === "sameAs" || p === "differentFrom") return true;
  return p === "a" && (CLASSES.includes(o) || o.startsWith("_:r"));
}

/** retracted adds base and delta, runs, then retracts delta. */
export function retracted(
  base: readonly T3[],
  delta: readonly T3[],
  mode: Mode,
): Outcome & { removed: Set<string> } {
  const r = new Reasoner();
  r.add([...base, ...delta].map(quad));
  r.run();
  const removed = r.retract(
    delta.map(quad),
    "complete",
    mode === "retract-full" ? { maxScope: 0 } : {},
  );
  return {
    ...outcome(r),
    removed: new Set(removed.filter((q) => !isSkolem(q)).map(key)),
  };
}

export interface Diff {
  /** missing is in the full run but not in the incremental one. */
  missing: string[];
  /** extra is in the incremental run but not in the full one. */
  extra: string[];
  missingInconsistencies: string[];
  extraInconsistencies: string[];
  /** wrongRemoved is where retract's reported removals differ from the truth. */
  wrongRemoved: string[];
}

function minus(a: Set<string>, b: Set<string>): string[] {
  return [...a].filter((x) => !b.has(x)).sort();
}

export function diff(
  base: readonly T3[],
  delta: readonly T3[],
  mode: Mode = "extend",
): Diff | null {
  let want: Outcome;
  let got: Outcome;
  let wrongRemoved: string[] = [];
  if (/^(union|graphs)-/.test(mode)) {
    const g = graphDiff(base, delta, mode);
    return Object.values(g).every((x) => x.length === 0) ? null : g;
  }
  if (mode === "extend") {
    want = full(base, delta);
    got = incremental(base, delta);
  } else {
    want = full(base, []);
    const all = full(base, delta);
    const r = retracted(base, delta, mode);
    got = r;
    const truth = minus(all.closure, want.closure);
    wrongRemoved = [
      ...minus(new Set(truth), r.removed),
      ...minus(r.removed, new Set(truth)),
    ];
  }
  const d = {
    missing: minus(want.closure, got.closure),
    extra: minus(got.closure, want.closure),
    missingInconsistencies: minus(want.inconsistencies, got.inconsistencies),
    extraInconsistencies: minus(got.inconsistencies, want.inconsistencies),
    wrongRemoved,
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
    d.wrongRemoved.length ? `wrong-removed[${preds(d.wrongRemoved)}]` : "",
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
  mode: Mode = "extend",
): { base: T3[]; delta: T3[] } {
  const still = (b: T3[], d: T3[]) => {
    const x = diff(b, d, mode);
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
  mode: Mode;
  cls: string;
  base: T3[];
  delta: T3[];
  diff: Diff;
}

/** runSeed splits the seed's graph at a seeded random point and compares. */
export function runSeed(seed: number, mode: Mode = "extend"): Failure | null {
  const triples = generate(seed);
  const rnd = prng(seed ^ 0x9E3779B9);
  const cut = 1 + Math.floor(rnd() * (triples.length - 1));
  let base = triples.slice(0, cut);
  let delta = triples.slice(cut);
  if (mode === "retract-instance") {
    delta = triples.filter((t) => isInstance(t) && rnd() < 0.4);
    if (delta.length === 0) return null;
    base = triples.filter((t) => !delta.includes(t));
  }
  const d = diff(base, delta, mode);
  if (d === null) return null;
  const cls = `${mode}: ${classify(d)}`;
  const small = shrink(base, delta, classify(d), mode);
  return {
    seed,
    mode,
    cls,
    ...small,
    diff: diff(small.base, small.delta, mode)!,
  };
}

export const fmt = (ts: readonly T3[]) =>
  ts.map((t) => t.join(" ")).join(" .\n") + " .";
