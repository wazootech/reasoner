/**
 * W3C OWL 2 RL conformance gate.
 *
 * Downloads the official OWL 2 test manifests for the RL profile (approved
 * and proposed) from w3.org into `.cache/owl2rl/`, runs every test whose
 * premise is given in RDF/XML, and compares the outcome with the committed
 * `expected-pass.json`. The test data is not vendored: the W3C publishes it
 * without separate redistribution terms, so each run fetches it (or reuses
 * the cache).
 *
 * A test passes when every one of its types holds:
 *
 * - positive entailment: the conclusion graph is contained in the closure
 *   (conclusion blank nodes match any term; `owl:sameAs` is reflexive);
 * - negative entailment: the non-conclusion graph is not contained in it;
 * - consistency / inconsistency: the reasoner reports no / some
 *   inconsistency.
 *
 * The run fails if a test listed in `expected-pass.json` fails. A test that
 * newly passes is reported so the list can grow with `--update`.
 *
 *     deno task test:w3c [--verbose]
 *     deno task test:w3c:update
 */
import type { Quad, Term } from "@rdfjs/types";
import { parseArgs } from "@std/cli/parse-args";
import { RdfXmlParser } from "rdfxml-streaming-parser";
import { dataFactory, termKey } from "@wazoo/sparql-engine/term";
import { Reasoner } from "@/mod.ts";
import { functionalSyntaxToQuads } from "./functional-syntax.ts";

const TEST = "http://www.w3.org/2007/OWL/testOntology#";
const RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const OWL = "http://www.w3.org/2002/07/owl#";
const MANIFESTS = [
  "https://www.w3.org/2009/11/owl-test/profile-RL.rdf",
  "https://www.w3.org/2009/11/owl-test/proposed/profile-RL.rdf",
];
const CACHE = new URL("../../.cache/owl2rl/", import.meta.url);
const EXPECTED = new URL("./expected-pass.json", import.meta.url);
const KNOWN_GAPS = new URL("./known-gaps.json", import.meta.url);

type Kind = "positive" | "negative" | "consistency" | "inconsistency";

const KINDS: Record<string, Kind> = {
  [`${TEST}PositiveEntailmentTest`]: "positive",
  [`${TEST}NegativeEntailmentTest`]: "negative",
  [`${TEST}ConsistencyTest`]: "consistency",
  [`${TEST}InconsistencyTest`]: "inconsistency",
};

interface TestCase {
  id: string;
  iri: string;
  status: string;
  kinds: Kind[];
  semantics: string[];
  premise?: string;
  conclusion?: string;
  nonConclusion?: string;
  fsPremise?: string;
  fsConclusion?: string;
  fsNonConclusion?: string;
}

async function cached(url: string): Promise<string> {
  const file = new URL(url.replace(/[^A-Za-z0-9.-]+/g, "_"), CACHE);
  try {
    return await Deno.readTextFile(file);
  } catch {
    const response = await fetch(url);
    if (!response.ok) throw new Error(`${url}: HTTP ${response.status}`);
    const text = await response.text();
    await Deno.mkdir(CACHE, { recursive: true });
    await Deno.writeTextFile(file, text);
    return text;
  }
}

function parseRdfXml(text: string, baseIRI: string): Promise<Quad[]> {
  return new Promise((resolve, reject) => {
    const quads: Quad[] = [];
    const parser = new RdfXmlParser({ baseIRI });
    parser.on("data", (quad: Quad) => quads.push(quad));
    parser.on("error", reject);
    parser.on("end", () => resolve(quads));
    parser.write(text);
    parser.end();
  });
}

function testCases(quads: Quad[]): TestCase[] {
  const bySubject = new Map<string, Quad[]>();
  for (const quad of quads) {
    const list = bySubject.get(quad.subject.value) ?? [];
    list.push(quad);
    bySubject.set(quad.subject.value, list);
  }
  const cases: TestCase[] = [];
  for (const [iri, statements] of bySubject) {
    const values = (property: string) =>
      statements.filter((quad) => quad.predicate.value === TEST + property)
        .map((quad) => quad.object.value);
    const kinds = statements
      .filter((quad) => quad.predicate.value === RDF_TYPE)
      .map((quad) => KINDS[quad.object.value])
      .filter((kind): kind is Kind => kind !== undefined);
    const id = values("identifier")[0];
    if (id === undefined || kinds.length === 0) continue;
    cases.push({
      id,
      iri,
      status: (values("status")[0] ?? "").replace(TEST, ""),
      kinds,
      semantics: values("semantics").map((s) => s.replace(TEST, "")),
      premise: values("rdfXmlPremiseOntology")[0],
      conclusion: values("rdfXmlConclusionOntology")[0],
      nonConclusion: values("rdfXmlNonConclusionOntology")[0],
      fsPremise: values("fsPremiseOntology")[0],
      fsConclusion: values("fsConclusionOntology")[0],
      fsNonConclusion: values("fsNonConclusionOntology")[0],
    });
  }
  return cases.sort((a, b) => a.id.localeCompare(b.id));
}

/**
 * contains checks that every pattern triple is in `closure`, treating the
 * pattern's blank nodes as variables (backtracking over their bindings).
 */
function contains(closure: Quad[], pattern: Quad[]): boolean {
  const keys = new Set(closure.map(tripleKey));
  const byPredicate = new Map<string, Quad[]>();
  for (const quad of closure) {
    const list = byPredicate.get(termKey(quad.predicate)) ?? [];
    list.push(quad);
    byPredicate.set(termKey(quad.predicate), list);
  }
  const reflexive = (quad: Quad, s: string, o: string) =>
    quad.predicate.value === `${OWL}sameAs` && s === o;
  const goals = [...pattern].sort((a, b) => blanks(a) - blanks(b));
  const match = (index: number, binding: Map<string, string>): boolean => {
    if (index === goals.length) return true;
    const goal = goals[index]!;
    const resolve = (term: Term) =>
      term.termType === "BlankNode" ? binding.get(term.value) : termKey(term);
    const [s, p, o] = [
      resolve(goal.subject),
      resolve(goal.predicate),
      resolve(goal.object),
    ];
    if (s !== undefined && p !== undefined && o !== undefined) {
      return (keys.has(`${s} ${p} ${o}`) || reflexive(goal, s, o)) &&
        match(index + 1, binding);
    }
    for (const candidate of byPredicate.get(p ?? "") ?? closure) {
      const next = new Map(binding);
      const bindTerm = (term: Term, value: Term): boolean => {
        if (term.termType !== "BlankNode") {
          return termKey(term) === termKey(value);
        }
        const bound = next.get(term.value);
        if (bound !== undefined) return bound === termKey(value);
        next.set(term.value, termKey(value));
        return true;
      };
      if (
        bindTerm(goal.subject, candidate.subject) &&
        bindTerm(goal.predicate, candidate.predicate) &&
        bindTerm(goal.object, candidate.object) &&
        match(index + 1, next)
      ) {
        return true;
      }
    }
    return false;
  };
  return match(0, new Map());
}

function blanks(quad: Quad): number {
  return [quad.subject, quad.predicate, quad.object]
    .filter((term) => term.termType === "BlankNode").length;
}

function tripleKey(quad: Quad): string {
  return `${termKey(quad.subject)} ${termKey(quad.predicate)} ${
    termKey(quad.object)
  }`;
}

const RDF_FIRST = "http://www.w3.org/1999/02/22-rdf-syntax-ns#first";
const RDF_REST = "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest";

/** N-ary axioms, and the binary property each member pair entails. */
const NARY: Record<string, string> = {
  [`${OWL}AllDifferent`]: `${OWL}differentFrom`,
  [`${OWL}AllDisjointClasses`]: `${OWL}disjointWith`,
  [`${OWL}AllDisjointProperties`]: `${OWL}propertyDisjointWith`,
};

/**
 * goal turns a conclusion graph into the triples to look for: the ontology
 * header goes (it names the document, not anything to entail), and each
 * n-ary axiom becomes the pairwise triples it is shorthand for, since its own
 * blank-node list is not something a closure can be expected to rebuild.
 */
function goal(quads: Quad[]): Quad[] {
  const bySubject = new Map<string, Quad[]>();
  for (const quad of quads) {
    const list = bySubject.get(termKey(quad.subject)) ?? [];
    list.push(quad);
    bySubject.set(termKey(quad.subject), list);
  }
  const object = (subject: Term, predicate: string) =>
    bySubject.get(termKey(subject))?.find((quad) =>
      quad.predicate.value === predicate
    )
      ?.object;
  const dropped = new Set<Quad>();
  const added: Quad[] = [];
  for (const quad of quads) {
    if (
      quad.predicate.value === RDF_TYPE &&
      quad.object.value === `${OWL}Ontology`
    ) {
      dropped.add(quad);
    }
    const pairwise = quad.predicate.value === RDF_TYPE
      ? NARY[quad.object.value]
      : undefined;
    if (pairwise === undefined) continue;
    const axiom = bySubject.get(termKey(quad.subject)) ?? [];
    const membersQuad = axiom.find((statement) =>
      statement.predicate.value === `${OWL}members` ||
      statement.predicate.value === `${OWL}distinctMembers`
    );
    if (membersQuad === undefined) continue;
    const members: Term[] = [];
    let node: Term | undefined = membersQuad.object;
    while (node !== undefined && node.termType === "BlankNode") {
      const cell = bySubject.get(termKey(node)) ?? [];
      for (const statement of cell) dropped.add(statement);
      const first = object(node, RDF_FIRST);
      if (first !== undefined) members.push(first);
      node = object(node, RDF_REST);
    }
    for (const statement of axiom) dropped.add(statement);
    for (let i = 0; i < members.length; i++) {
      for (let j = i + 1; j < members.length; j++) {
        added.push(dataFactory.quad(
          members[i] as Quad["subject"],
          dataFactory.namedNode(pairwise),
          members[j] as Quad["object"],
        ));
      }
    }
  }
  return [...quads.filter((quad) => !dropped.has(quad)), ...added];
}

/** ANNOTATION_PROPERTIES are the built-in annotation properties of OWL 2. */
const ANNOTATION_PROPERTIES = new Set([
  "http://www.w3.org/2000/01/rdf-schema#label",
  "http://www.w3.org/2000/01/rdf-schema#comment",
  "http://www.w3.org/2000/01/rdf-schema#seeAlso",
  "http://www.w3.org/2000/01/rdf-schema#isDefinedBy",
  `${OWL}versionInfo`,
  `${OWL}priorVersion`,
  `${OWL}backwardCompatibleWith`,
  `${OWL}incompatibleWith`,
  `${OWL}deprecated`,
]);

/**
 * withoutAnnotations drops the annotation assertions of a conclusion when the
 * test is for the Direct Semantics alone, which ignores annotations in the
 * entailed ontology (the RDF-Based Semantics does not).
 */
function withoutAnnotations(
  conclusion: Quad[],
  premise: Quad[],
  test: TestCase,
): Quad[] {
  if (
    test.semantics.includes("RDF-BASED") || !test.semantics.includes("DIRECT")
  ) {
    return conclusion;
  }
  const annotation = new Set(ANNOTATION_PROPERTIES);
  for (const quad of [...premise, ...conclusion]) {
    if (
      quad.predicate.value === RDF_TYPE &&
      quad.object.value === `${OWL}AnnotationProperty`
    ) annotation.add(quad.subject.value);
  }
  return conclusion.filter((quad) => !annotation.has(quad.predicate.value));
}

/** load parses one of a test's ontologies from RDF/XML, else functional syntax. */
async function load(
  test: TestCase,
  part: "premise" | "conclusion" | "nonConclusion",
): Promise<Quad[] | undefined> {
  const xml = test[part];
  if (xml !== undefined) return await parseRdfXml(xml, `${test.iri}/${part}`);
  const fs = {
    premise: test.fsPremise,
    conclusion: test.fsConclusion,
    nonConclusion: test.fsNonConclusion,
  }[part];
  return fs === undefined ? undefined : functionalSyntaxToQuads(fs);
}

/**
 * withImports adds the closure of `owl:imports` to a premise. Each imported
 * document is fetched once (and cached), with its own IRI as the base.
 */
async function withImports(quads: Quad[]): Promise<Quad[]> {
  const out = [...quads];
  const seen = new Set<string>();
  for (let i = 0; i < out.length; i++) {
    const quad = out[i]!;
    if (quad.predicate.value !== `${OWL}imports`) continue;
    const iri = quad.object.value;
    if (seen.has(iri)) continue;
    seen.add(iri);
    out.push(...await parseRdfXml(await cached(iri), iri));
  }
  return out;
}

type Outcome = { ok: true } | { ok: false; reason: string };

async function run(test: TestCase): Promise<Outcome> {
  const own = await load(test, "premise");
  if (own === undefined) {
    return { ok: false, reason: "no RDF/XML or functional-syntax premise" };
  }
  const premise = await withImports(own);
  const reasoner = new Reasoner();
  reasoner.add(premise);
  reasoner.run();
  const closure = [...premise, ...reasoner.closure("complete")];
  const inconsistent = reasoner.inconsistencies().length > 0;
  for (const kind of test.kinds) {
    if (kind === "consistency" && inconsistent) {
      return { ok: false, reason: "reported an inconsistency" };
    }
    if (kind === "inconsistency" && !inconsistent) {
      return { ok: false, reason: "found no inconsistency" };
    }
    if (kind === "positive") {
      const parsed = await load(test, "conclusion");
      if (parsed === undefined) {
        return { ok: false, reason: "no RDF/XML conclusion" };
      }
      const conclusion = withoutAnnotations(
        goal(parsed),
        premise,
        test,
      );
      // An inconsistent premise entails everything.
      if (!inconsistent && !contains(closure, conclusion)) {
        if (explain === test.id) {
          const have = new Set(closure.map(tripleKey));
          console.log(`PREMISE:\n${test.premise}`);
          console.log(`CONCLUSION:\n${test.conclusion}`);
          const missing = conclusion.filter((quad) =>
            blanks(quad) === 0 && !have.has(tripleKey(quad))
          );
          console.log(
            `MISSING (blank-free):\n${missing.map(tripleKey).join("\n")}`,
          );
        }
        return { ok: false, reason: "conclusion not entailed" };
      }
    }
    if (kind === "negative") {
      const parsed = await load(test, "nonConclusion");
      if (parsed === undefined) {
        return { ok: false, reason: "no RDF/XML non-conclusion" };
      }
      const nonConclusion = goal(parsed);
      if (inconsistent || contains(closure, nonConclusion)) {
        return { ok: false, reason: "non-conclusion entailed" };
      }
    }
  }
  return { ok: true };
}

const args = parseArgs(Deno.args, {
  boolean: ["update", "verbose"],
  string: ["explain"],
});
const { update, verbose, explain } = args;
const tests = new Map<string, TestCase>();
for (const manifest of MANIFESTS) {
  for (
    const test of testCases(await parseRdfXml(await cached(manifest), manifest))
  ) {
    tests.set(test.id, test);
  }
}
const knownGaps: Record<string, string> = JSON.parse(
  await Deno.readTextFile(KNOWN_GAPS),
);
const expected = new Set<string>(JSON.parse(await Deno.readTextFile(EXPECTED)));
const passed: string[] = [];
const regressions: string[] = [];
const newlyPassing: string[] = [];
const staleGaps: string[] = [];
const reasons = new Map<string, number>();
for (const test of tests.values()) {
  let outcome: Outcome;
  try {
    outcome = await run(test);
  } catch (error) {
    if (verbose) console.error(error);
    outcome = {
      ok: false,
      reason: `error: ${(error as Error).message.split("\n")[0]}`,
    };
  }
  if (outcome.ok) {
    passed.push(test.id);
    if (!expected.has(test.id)) newlyPassing.push(test.id);
    if (test.id in knownGaps) staleGaps.push(test.id);
  } else {
    const reason = test.id in knownGaps
      ? "known gap (see known-gaps.json)"
      : outcome.reason.startsWith("error")
      ? "parse or run error"
      : outcome.reason;
    reasons.set(reason, (reasons.get(reason) ?? 0) + 1);
    if (expected.has(test.id)) {
      regressions.push(`${test.id}: ${outcome.reason}`);
    }
    if (verbose) {
      console.log(`FAIL ${test.kinds.join("+")} ${test.id}: ${outcome.reason}`);
    }
  }
}

console.log(`OWL 2 RL conformance: ${passed.length}/${tests.size} pass`);
for (const [reason, count] of [...reasons].sort((a, b) => b[1] - a[1])) {
  console.log(`  ${count} × ${reason}`);
}
if (update) {
  await Deno.writeTextFile(
    EXPECTED,
    JSON.stringify(passed.sort(), null, 2) + "\n",
  );
  console.log(`Wrote ${passed.length} passing tests to expected-pass.json.`);
} else {
  if (newlyPassing.length > 0) {
    console.log(
      `Newly passing (run with --update to record): ${newlyPassing.join(", ")}`,
    );
  }
  if (staleGaps.length > 0) {
    console.error(
      `Passing but listed in known-gaps.json: ${staleGaps.join(", ")}`,
    );
    Deno.exit(1);
  }
  if (regressions.length > 0) {
    console.error(`Regressions:\n  ${regressions.join("\n  ")}`);
    Deno.exit(1);
  }
}
