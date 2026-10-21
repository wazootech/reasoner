/**
 * Parity gate: the closure this package computes against the closure the
 * Wiki computed with `rdfjs-inference-engine` (Eyeling) before it, triple for
 * triple, on asserted graphs dumped to N-Triples.
 *
 * The reference closure is computed exactly as the Wiki's `applyInference`
 * did: the baked OWL 2 RL ruleset without dt-eq, the ontology triples as the
 * engine's vocabulary, the equality rules only when some term can derive
 * `owl:sameAs`, and the engine's internal and inconsistency namespaces
 * filtered out.
 *
 * Every difference must be one of the {@link DIVERGENCES}; anything else
 * fails the run.
 *
 *     deno task test:parity [file.nt ...]
 */
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import type { Quad, Term } from "@rdfjs/types";
import { InferenceEngine } from "rdfjs-inference-engine";
import { parseTurtleQuads } from "@wazoo/sparql-engine/parser";
import { dataFactory, termKey } from "@wazoo/sparql-engine/term";
import { COMPLEMENT_PREFIX, Reasoner } from "@/mod.ts";

const RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS = "http://www.w3.org/2000/01/rdf-schema#";
const OWL = "http://www.w3.org/2002/07/owl#";
const EYELING_SKOLEM = "https://eyereasoner.github.io/.well-known/genid/";
const ENGINE_NAMESPACES = [
  "https://www.pieter.pm/rdfjs-inference-engine/ns/internal#",
  "https://www.pieter.pm/rdfjs-inference-engine/ns/inconsistencies#",
];

/**
 * DIVERGENCES are the differences from the old closure this package makes on
 * purpose. Each classifies a triple present on one side only.
 */
const DIVERGENCES: readonly {
  name: string;
  side: "reference" | "reasoner";
  matches: (quad: Quad, reference: Closure) => boolean;
}[] = [
  {
    // The reference reasoned over the ontology separately from the instance
    // data, so an owl:sameAs asserted as data never rewrote an ontology
    // triple (eq-rep-s/p/o). Matched exactly: replacing the triple's terms
    // with owl:sameAs equivalents of the reference closure must give a
    // triple the reference has.
    name: "eq-rep applied to an ontology triple (reference skipped it)",
    side: "reasoner",
    matches: (quad, reference) => {
      for (const s of reference.equivalents(quad.subject)) {
        for (const p of reference.equivalents(quad.predicate)) {
          for (const o of reference.equivalents(quad.object)) {
            if (reference.has(`${s} ${p} ${o}`)) return true;
          }
        }
      }
      return false;
    },
  },
];

/** Closure is a keyed closure plus its owl:sameAs classes. */
interface Closure {
  readonly size: number;
  has(key: string): boolean;
  keys(): IterableIterator<string>;
  get(key: string): Quad | undefined;
  /** equivalents lists the keys of `term` and of every term sameAs it. */
  equivalents(term: Term): string[];
}

const require = createRequire(import.meta.url);
const ENGINE_ROOT = dirname(
  dirname(dirname(require.resolve("rdfjs-inference-engine"))),
);
const RULES = Deno.readTextFileSync(
  join(ENGINE_ROOT, "rules/owl2rl/owl2rl-eyeling.n3"),
)
  .replaceAll("\r\n", "\n");

const DT_EQ_RULE = `{ ?n1 internal:term ?lt1 .
  ?n2 internal:term ?lt2 .
  ?lt1 log:notEqualTo ?lt2 .
  ?lt1 dt:datatype ?dt1 .
  ?dt1 log:notEqualTo xsd:string .
  ?dt1 log:notEqualTo rdf:langString .
  ?lt1 dt:sameValueAs ?lt2 . }
=> { ?lt1 owl:sameAs ?lt2 . } .`;

const RULE_PATTERN = new RegExp(
  String.raw`\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}\s*=>\s*` +
    String.raw`\{[^{}]*(?:\{[^{}]*\}[^{}]*)*\}\s*\.`,
  "g",
);

function withoutRule(rules: string, rule: string): string {
  const parts = rules.split(rule);
  if (parts.length !== 2) throw new Error("dt-eq rule not found exactly once");
  return parts.join("");
}

const FULL_RULES = withoutRule(RULES, DT_EQ_RULE);
const RULES_WITHOUT_EQUALITY = FULL_RULES.replace(
  RULE_PATTERN,
  (rule) => (rule.split("=>")[0] ?? "").includes("owl:sameAs") ? "" : rule,
);

const SAME_AS_SOURCES = new Set(
  [
    "sameAs",
    "NamedIndividual",
    "Nothing",
    "FunctionalProperty",
    "InverseFunctionalProperty",
    "hasKey",
    "maxCardinality",
    "maxQualifiedCardinality",
  ].map((name) => OWL + name),
);

function isOntologyTriple(quad: Quad): boolean {
  const predicate = quad.predicate.value;
  if (predicate === `${RDF}type`) {
    const type = quad.object.value;
    return type.startsWith(OWL) || type.startsWith(RDFS) ||
      type === `${RDF}Property`;
  }
  if (predicate === `${RDF}first` || predicate === `${RDF}rest`) return true;
  if (predicate.startsWith(RDFS)) {
    return ![
      `${RDFS}label`,
      `${RDFS}comment`,
      `${RDFS}seeAlso`,
      `${RDFS}isDefinedBy`,
    ]
      .includes(predicate);
  }
  if (predicate.startsWith(OWL)) {
    return predicate !== `${OWL}sameAs` && predicate !== `${OWL}differentFrom`;
  }
  return false;
}

function referenceClosure(asserted: Quad[]): Quad[] {
  const mayDeriveSameAs = asserted.some((quad) =>
    SAME_AS_SOURCES.has(quad.subject.value) ||
    SAME_AS_SOURCES.has(quad.predicate.value) ||
    SAME_AS_SOURCES.has(quad.object.value)
  );
  const engine = new InferenceEngine();
  engine.load(
    [{
      n3: mayDeriveSameAs ? FULL_RULES : RULES_WITHOUT_EQUALITY,
      label: "rules/owl2rl",
    }],
    asserted.filter(isOntologyTriple),
    { selectRuntimeRules: false },
  );
  const internal = (term: Term) =>
    ENGINE_NAMESPACES.some((namespace) => term.value.startsWith(namespace));
  return [...asserted, ...engine.getStaticClosure(), ...engine.infer(asserted)]
    .filter(
      (quad: Quad) =>
        !internal(quad.subject) && !internal(quad.predicate) &&
        !internal(quad.object),
    );
}

/**
 * normalize keys a closure's triples, renaming each complement skolem to the
 * class it complements so the two engines' skolem IRIs compare equal.
 */
function normalize(closure: Iterable<Quad>): Closure {
  const quads = [...closure];
  const complements = new Map<string, string>();
  for (const quad of quads) {
    if (quad.predicate.value !== `${OWL}complementOf`) continue;
    const skolem = quad.subject.value;
    if (
      skolem.startsWith(EYELING_SKOLEM) || skolem.startsWith(COMPLEMENT_PREFIX)
    ) {
      complements.set(skolem, `complement(${termKey(quad.object)})`);
    }
  }
  const rename = (term: Term): string =>
    term.termType === "NamedNode" && complements.has(term.value)
      ? complements.get(term.value)!
      : termKey(term);
  const keyed = new Map<string, Quad>();
  const same = new Map<string, Set<string>>();
  for (const quad of quads) {
    const [s, p, o] = [
      rename(quad.subject),
      rename(quad.predicate),
      rename(quad.object),
    ];
    keyed.set(`${s} ${p} ${o}`, quad);
    if (quad.predicate.value === `${OWL}sameAs`) {
      for (const [a, b] of [[s, o], [o, s]]) {
        const set = same.get(a!) ?? new Set([a!]);
        set.add(b!);
        same.set(a!, set);
      }
    }
  }
  return {
    size: keyed.size,
    has: (key) => keyed.has(key),
    keys: () => keyed.keys(),
    get: (key) => keyed.get(key),
    equivalents: (term) => {
      const key = rename(term);
      return [...(same.get(key) ?? [key])];
    },
  };
}

function compare(name: string, asserted: Quad[]): boolean {
  let start = performance.now();
  const reference = normalize(referenceClosure(asserted));
  const referenceMs = performance.now() - start;
  start = performance.now();
  const reasoner = new Reasoner();
  reasoner.add(asserted);
  reasoner.run();
  const ours = normalize([...asserted, ...reasoner.closure("application")]);
  const oursMs = performance.now() - start;

  const counts = new Map<string, number>();
  const unexplained: string[] = [];
  const classify = (
    side: "reference" | "reasoner",
    key: string,
    quad: Quad,
  ) => {
    const divergence = DIVERGENCES.find((entry) =>
      entry.side === side && entry.matches(quad, reference)
    );
    if (divergence) {
      counts.set(divergence.name, (counts.get(divergence.name) ?? 0) + 1);
    } else unexplained.push(`${side === "reference" ? "-" : "+"} ${key}`);
  };
  for (const key of reference.keys()) {
    if (!ours.has(key)) classify("reference", key, reference.get(key)!);
  }
  for (const key of ours.keys()) {
    if (!reference.has(key)) classify("reasoner", key, ours.get(key)!);
  }

  console.log(
    `${name}: asserted ${asserted.length}, reference ${reference.size} ` +
      `(${referenceMs.toFixed(0)} ms), reasoner ${ours.size} (${
        oursMs.toFixed(0)
      } ms)`,
  );
  for (const [divergence, count] of counts) {
    console.log(`  ~ ${count} × ${divergence}`);
  }
  for (const line of unexplained.slice(0, 20)) console.log(`  ${line}`);
  if (unexplained.length > 20) {
    console.log(`  … ${unexplained.length - 20} more`);
  }
  return unexplained.length === 0;
}

const DEFAULT_DIR = new URL("./corpora/", import.meta.url);
const files = Deno.args.length > 0
  ? Deno.args
  : [...Deno.readDirSync(DEFAULT_DIR)]
    .filter((entry) => entry.name.endsWith(".nt"))
    .map((entry) =>
      new URL(entry.name, DEFAULT_DIR).pathname.replace(/^\/([A-Za-z]:)/, "$1")
    )
    .sort();

let ok = true;
for (const file of files) {
  const name = file.split(/[\\/]/).pop()!.replace(/\.nt$/, "");
  const asserted = parseTurtleQuads(Deno.readTextFileSync(file)).map((quad) =>
    dataFactory.quad(quad.subject, quad.predicate, quad.object)
  );
  ok = compare(name, asserted) && ok;
}
if (!ok) {
  console.error(
    "Parity failed: differences outside the documented divergences.",
  );
  Deno.exit(1);
}
