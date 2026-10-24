import { assert, assertEquals, assertFalse } from "@std/assert";
import { parseTurtleQuads } from "@wazoo/sparql-engine/parser";
import { dataFactory } from "@wazoo/sparql-engine/term";
import type { Quad } from "@rdfjs/types";
import { DERIVED_GRAPH, Reasoner, type ReasonerOptions } from "@/mod.ts";

const EX = "https://reasoner.example/";
const OWL = "http://www.w3.org/2002/07/owl#";
const RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const PREFIXES = `@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <${OWL}> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix ex: <${EX}> .
`;

function quads(turtle: string): Quad[] {
  return parseTurtleQuads(PREFIXES + turtle);
}

function reason(turtle: string): Reasoner {
  const reasoner = new Reasoner();
  reasoner.add(quads(turtle));
  reasoner.run();
  return reasoner;
}

const ex = (name: string) => dataFactory.namedNode(EX + name);
const iri = (value: string) => dataFactory.namedNode(value);

function entails(reasoner: Reasoner, s: string, p: string, o: string): boolean {
  const term = (name: string) => name.includes(":") ? iri(name) : ex(name);
  return reasoner.has(term(s), term(p), term(o));
}

Deno.test("subclass, inverse, and transitive axioms", () => {
  const reasoner = reason(`
ex:Student rdfs:subClassOf ex:Person .
ex:Person rdfs:subClassOf ex:Agent .
ex:hasChild owl:inverseOf ex:hasParent .
ex:ancestorOf a owl:TransitiveProperty .
ex:alice a ex:Student ; ex:hasChild ex:carol .
ex:a1 ex:ancestorOf ex:a2 . ex:a2 ex:ancestorOf ex:a3 . ex:a3 ex:ancestorOf ex:a4 .
`);
  assert(entails(reasoner, "alice", RDF_TYPE, "Agent"));
  assert(
    entails(
      reasoner,
      "Student",
      "http://www.w3.org/2000/01/rdf-schema#subClassOf",
      "Agent",
    ),
  );
  assert(entails(reasoner, "carol", "hasParent", "alice"));
  assert(entails(reasoner, "a1", "ancestorOf", "a4"));
  assertFalse(entails(reasoner, "a4", "ancestorOf", "a1"));
});

Deno.test("owl:sameAs merges terms and the closure expands each class", () => {
  const reasoner = reason(`
ex:a owl:sameAs ex:b .
ex:b owl:sameAs ex:c .
ex:a ex:knows ex:d .
ex:e ex:likes ex:c .
`);
  const closure = new Set(
    [...reasoner.closure()].map((quad) =>
      `${quad.subject.value} ${quad.predicate.value} ${quad.object.value}`
    ),
  );
  for (const x of ["a", "b", "c"]) {
    assert(closure.has(`${EX}${x} ${EX}knows ${EX}d`), `${x} knows d`);
    assert(closure.has(`${EX}e ${EX}likes ${EX}${x}`), `e likes ${x}`);
    for (const y of ["a", "b", "c"]) {
      assert(closure.has(`${EX}${x} ${OWL}sameAs ${EX}${y}`), `${x} = ${y}`);
    }
  }
});

Deno.test("a functional property derives owl:sameAs", () => {
  const reasoner = reason(`
ex:hasMother a owl:FunctionalProperty .
ex:gus ex:hasMother ex:m1 , ex:m2 .
ex:m1 ex:livesIn ex:town .
`);
  assert(entails(reasoner, "m1", `${OWL}sameAs`, "m2"));
  assert(entails(reasoner, "m2", "livesIn", "town"));
});

Deno.test("property chains of any length", () => {
  const reasoner = reason(`
ex:p4 owl:propertyChainAxiom ( ex:a ex:b ex:c ex:d ) .
ex:p2 owl:propertyChainAxiom ( ex:a ex:b ) .
ex:x0 ex:a ex:x1 . ex:x1 ex:b ex:x2 . ex:x2 ex:c ex:x3 . ex:x3 ex:d ex:x4 .
`);
  assert(entails(reasoner, "x0", "p2", "x2"));
  assert(entails(reasoner, "x0", "p4", "x4"));
  assertFalse(entails(reasoner, "x1", "p4", "x4"));
});

Deno.test("intersections, unions, and keys", () => {
  const reasoner = reason(`
ex:Both owl:intersectionOf ( ex:A ex:B ex:C ex:D ex:E ) .
ex:Either owl:unionOf ( ex:A ex:F ) .
ex:i a ex:A , ex:B , ex:C , ex:D , ex:E .
ex:j a ex:A , ex:B .
ex:k a ex:F .
ex:Person owl:hasKey ( ex:ssn ex:country ) .
ex:u1 a ex:Person ; ex:ssn "1" ; ex:country ex:nl .
ex:u2 a ex:Person ; ex:ssn "1" ; ex:country ex:nl .
ex:u3 a ex:Person ; ex:ssn "1" ; ex:country ex:be .
`);
  assert(entails(reasoner, "i", RDF_TYPE, "Both"));
  assertFalse(entails(reasoner, "j", RDF_TYPE, "Both"));
  assert(entails(reasoner, "k", RDF_TYPE, "Either"));
  assert(entails(reasoner, "u1", `${OWL}sameAs`, "u2"));
  assertFalse(entails(reasoner, "u1", `${OWL}sameAs`, "u3"));
});

Deno.test("inconsistencies are reported, not materialized", () => {
  const reasoner = reason(`
ex:Cat owl:disjointWith ex:Dog .
ex:rex a ex:Cat , ex:Dog .
ex:age a owl:FunctionalProperty .
ex:tom ex:age "3"^^xsd:integer , "4"^^xsd:integer .
`);
  const rules = reasoner.inconsistencies().map((report) => report.rule).sort();
  assert(rules.includes("cax-dw"), rules.join());
  assert(rules.includes("eq-diff1"), rules.join());
});

Deno.test("literals are typed within their own datatype family", () => {
  const reasoner = reason(`
ex:x ex:count "5"^^xsd:integer ; ex:name "five" ; ex:on "2026-01-01"^^xsd:date .
`);
  const has = (lexical: string, datatype: string, type: string) =>
    reasoner.has(
      dataFactory.literal(lexical, iri(datatype)),
      iri(RDF_TYPE),
      iri(type),
    );
  const XSD = "http://www.w3.org/2001/XMLSchema#";
  assert(has("5", `${XSD}integer`, `${XSD}integer`));
  assert(has("5", `${XSD}integer`, `${XSD}byte`));
  assert(has("5", `${XSD}integer`, `${XSD}decimal`));
  assertFalse(has("5", `${XSD}integer`, `${XSD}string`));
  assert(has("five", `${XSD}string`, `${XSD}string`));
  assertFalse(has("2026-01-01", `${XSD}date`, `${XSD}string`));
});

Deno.test("extend returns exactly what new triples add", () => {
  const reasoner = reason(`
ex:Student rdfs:subClassOf ex:Person .
ex:alice a ex:Student .
ex:hasMother a owl:FunctionalProperty .
ex:gus ex:hasMother ex:m1 .
ex:m1 ex:livesIn ex:town .
`);
  const before = new Set([...reasoner.closure()].map(key));
  const added = reasoner.extend(quads(`
ex:bob a ex:Student .
ex:alice a ex:Student .
ex:gus ex:hasMother ex:m2 .
`));
  const after = new Set([...reasoner.closure()].map(key));
  const expected = [...after].filter((triple) => !before.has(triple)).sort();
  assertEquals([...new Set(added.map(key))].sort(), expected);
  assert(expected.includes(`${EX}m2 ${EX}livesIn ${EX}town`));
  assert(expected.includes(`${EX}bob ${RDF_TYPE} ${EX}Person`));
});

function key(quad: Quad): string {
  return `${quad.subject.value} ${quad.predicate.value} ${quad.object.value}`;
}

Deno.test("functional-property values that are literals are not paired as differentFrom", () => {
  const reasoner = reason(`
ex:id a owl:FunctionalProperty .
ex:a ex:id "1"^^xsd:integer .
ex:b ex:id "2"^^xsd:integer .
ex:c ex:id "1"^^xsd:integer .
ex:d ex:id ex:v1 .
ex:e ex:id ex:v2 .
`);
  // Distinct literal values would pair every subject with every other (issue
  // #7), so no differentFrom is derived; a merge of such subjects is still
  // inconsistent (the tests below).
  assertFalse(entails(reasoner, "a", `${OWL}differentFrom`, "b"));
  assertFalse(entails(reasoner, "b", `${OWL}differentFrom`, "a"));
  assertFalse(entails(reasoner, "a", `${OWL}differentFrom`, "c"));
  assertFalse(entails(reasoner, "d", `${OWL}differentFrom`, "e"));
});

Deno.test("closure time stays near-linear on owl:sameAs-heavy graphs", () => {
  const time = (people: number): number => {
    const turtle = ["ex:hasId a owl:FunctionalProperty ."];
    for (let i = 0; i < people; i++) {
      turtle.push(`ex:p${i} a ex:Person ; ex:hasId ex:v${i} , ex:w${i} .`);
      turtle.push(
        i > 0 && i % 2 === 0
          ? `ex:p${i} owl:sameAs ex:p${i - 1} .`
          : `ex:p${i} ex:knows ex:p${i + 1} .`,
      );
    }
    const reasoner = new Reasoner();
    reasoner.add(quads(turtle.join("\n")));
    const start = performance.now();
    reasoner.run();
    return performance.now() - start;
  };
  time(200); // warm up
  const small = time(1000);
  const large = time(8000);
  // 8x the data: linear is ~8x, the quadratic behaviour was ~64x. Allow slack.
  assert(large < Math.max(small, 20) * 24, `${small} ms -> ${large} ms`);
});

/** incrementalMatchesFull runs base then extend(delta) against one full run. */
function incrementalMatchesFull(base: string, delta: string): Reasoner {
  const incremental = reason(base);
  incremental.extend(quads(delta));
  const full = reason(base + delta);
  const closure = (reasoner: Reasoner) =>
    [...reasoner.closure()].map(key).sort();
  const rules = (reasoner: Reasoner) =>
    [...new Set(reasoner.inconsistencies().map((i) => i.rule))].sort();
  assertEquals(closure(incremental), closure(full));
  assertEquals(rules(incremental), rules(full));
  return incremental;
}

Deno.test("a second literal joining a class late makes it differentFrom itself", () => {
  const reasoner = incrementalMatchesFull(
    `ex:i0 owl:sameAs "2" .`,
    `ex:i0 owl:sameAs "1" .`,
  );
  assert(reasoner.inconsistencies().some((i) => i.rule === "eq-diff1"));
});

Deno.test("values that become different literals late make their merge inconsistent", () => {
  const reasoner = incrementalMatchesFull(
    `ex:p0 a owl:FunctionalProperty . ex:a ex:p0 ex:y . ex:b ex:p0 ex:z .`,
    `ex:y owl:sameAs "1" . ex:z owl:sameAs "2" . ex:y owl:sameAs ex:z .`,
  );
  assert(reasoner.inconsistencies().some((i) => i.rule === "eq-diff1"));
});

Deno.test("a literal joining a class late types the class", () => {
  const reasoner = incrementalMatchesFull(
    `ex:i1 owl:sameAs ex:i0 .`,
    `ex:i1 owl:sameAs "2" .`,
  );
  const rdfsLiteral = iri("http://www.w3.org/2000/01/rdf-schema#Literal");
  assert(reasoner.has(ex("i0"), iri(RDF_TYPE), rdfsLiteral));
});

Deno.test("an inverse-functional merge that adds a late literal still reports eq-diff1", () => {
  const reasoner = incrementalMatchesFull(
    `ex:p0 owl:inverseOf ex:p3 . ex:i1 ex:p0 "1" .
ex:p0 owl:inverseOf ex:p1 . ex:p1 a owl:InverseFunctionalProperty .
ex:p0 rdfs:subPropertyOf ex:p1 . ex:i0 owl:sameAs "2" .`,
    `ex:i1 ex:p3 ex:i0 .`,
  );
  assert(reasoner.inconsistencies().some((i) => i.rule === "eq-diff1"));
});

Deno.test("a plain string in the range of a numeric datatype is inconsistent", () => {
  const reasoner = reason(`
ex:age rdfs:range xsd:integer .
ex:a ex:age "aString" .
`);
  assert(reasoner.inconsistencies().some((i) => i.rule === "dt-not-type"));
});

Deno.test("a plain string in the range of xsd:string is consistent", () => {
  const reasoner = reason(`
ex:name rdfs:range xsd:string .
ex:a ex:name "Ada" .
`);
  assertEquals(reasoner.inconsistencies(), []);
});

Deno.test("positive and negative zero are distinct float values", () => {
  const reasoner = reason(`
ex:n a owl:FunctionalProperty .
ex:m ex:n "+0.0"^^xsd:float, "-0.0"^^xsd:float .
`);
  assert(reasoner.inconsistencies().length > 0);
});

Deno.test("equal float zeros stay one value", () => {
  const reasoner = reason(`
ex:n a owl:FunctionalProperty .
ex:m ex:n "0.0"^^xsd:float, "0"^^xsd:float .
`);
  assertEquals(reasoner.inconsistencies(), []);
});

function closureKeys(reasoner: Reasoner): string[] {
  return [...reasoner.closure("complete")].map((q) =>
    [q.subject, q.predicate, q.object].map((t) =>
      t.termType === "Literal" ? `"${t.value}"^^${t.datatype.value}` : t.value
    ).join(" ")
  ).sort();
}

Deno.test("retract removes a triple and what only it entailed", () => {
  const reasoner = reason(`
ex:Student rdfs:subClassOf ex:Person .
ex:alice a ex:Student .
`);
  assert(entails(reasoner, "alice", RDF_TYPE, "Person"));
  const removed = reasoner.retract(
    quads(`ex:Student rdfs:subClassOf ex:Person .`),
  );
  assertFalse(entails(reasoner, "alice", RDF_TYPE, "Person"));
  assert(entails(reasoner, "alice", RDF_TYPE, "Student"));
  assert(
    removed.some((q) =>
      q.subject.value === EX + "alice" && q.object.value === EX + "Person"
    ),
  );
});

Deno.test("retract keeps what another derivation still entails", () => {
  const reasoner = reason(`
ex:A rdfs:subClassOf ex:C . ex:B rdfs:subClassOf ex:C .
ex:x a ex:A, ex:B .
`);
  reasoner.retract(quads(`ex:A rdfs:subClassOf ex:C .`));
  assert(entails(reasoner, "x", RDF_TYPE, "C"));
});

Deno.test("retract splits an owl:sameAs class", () => {
  const reasoner = reason(`
ex:a owl:sameAs ex:b . ex:b owl:sameAs ex:c .
ex:a ex:p ex:o .
`);
  assert(entails(reasoner, "c", "p", "o"));
  reasoner.retract(quads(`ex:b owl:sameAs ex:c .`));
  assertFalse(entails(reasoner, "c", "p", "o"));
  assert(entails(reasoner, "b", "p", "o"));
});

Deno.test("retract ignores a triple that was only entailed", () => {
  const reasoner = reason(`
ex:Student rdfs:subClassOf ex:Person .
ex:alice a ex:Student .
`);
  assertEquals(reasoner.retract(quads(`ex:alice a ex:Person .`)), []);
  assert(entails(reasoner, "alice", RDF_TYPE, "Person"));
});

Deno.test("retract equals a fresh run, locally and over the whole closure", () => {
  const graph = `
ex:Student rdfs:subClassOf ex:Person .
ex:alice a ex:Student ; ex:knows ex:bob .
ex:bob owl:sameAs ex:robert .
ex:knows a owl:SymmetricProperty .
ex:other a ex:Thing ; ex:p ex:q .
`;
  const rest = `
ex:Student rdfs:subClassOf ex:Person .
ex:alice a ex:Student .
ex:knows a owl:SymmetricProperty .
ex:other a ex:Thing ; ex:p ex:q .
`;
  const fresh = closureKeys(reason(rest));
  for (const options of [{}, { maxScope: 0 }]) {
    const reasoner = reason(graph);
    reasoner.retract(
      quads(`ex:bob owl:sameAs ex:robert .`),
      "complete",
      options,
    );
    reasoner.retract(quads(`ex:alice ex:knows ex:bob .`), "complete", options);
    assertEquals(closureKeys(reasoner), fresh);
  }
});

Deno.test("retract recomputes only the component of the triple", () => {
  const reasoner = new Reasoner();
  const lines: string[] = [];
  for (let i = 0; i < 50; i++) {
    lines.push(`ex:c${i} rdfs:subClassOf ex:d${i} . ex:i${i} a ex:c${i} .`);
  }
  reasoner.add(quads(lines.join("\n")));
  reasoner.run();
  const before = reasoner.statistics.derivations;
  reasoner.retract(quads(`ex:c7 rdfs:subClassOf ex:d7 .`));
  // A whole-closure rebuild would derive every component again.
  assert(reasoner.statistics.derivations - before < before / 5);
  assertFalse(entails(reasoner, "i7", RDF_TYPE, "d7"));
  assert(entails(reasoner, "i8", RDF_TYPE, "d8"));
});

Deno.test("an extended triple can be retracted", () => {
  const reasoner = reason(`ex:Student rdfs:subClassOf ex:Person .`);
  reasoner.extend(quads(`ex:alice a ex:Student .`));
  assert(entails(reasoner, "alice", RDF_TYPE, "Person"));
  reasoner.retract(quads(`ex:alice a ex:Student .`));
  assertFalse(entails(reasoner, "alice", RDF_TYPE, "Person"));
});

Deno.test("retract keeps schema triples whose terms are also individuals", () => {
  const cases: [string, string, string][] = [
    [
      `ex:C rdfs:subClassOf ex:D .`,
      `ex:C ex:knows ex:b .`,
      `ex:C rdfs:subClassOf ex:D .`,
    ],
    [
      `ex:C rdfs:subClassOf ex:E . ex:D rdfs:subClassOf ex:F .`,
      `ex:C owl:sameAs ex:D .`,
      `ex:C rdfs:subClassOf ex:E . ex:D rdfs:subClassOf ex:F .`,
    ],
    [
      `ex:p rdfs:domain ex:E . ex:q rdfs:range ex:F .`,
      `ex:p owl:sameAs ex:q .`,
      `ex:p rdfs:domain ex:E . ex:q rdfs:range ex:F .`,
    ],
  ];
  for (const [base, gone, rest] of cases) {
    for (const options of [{}, { maxScope: 0 }]) {
      const reasoner = reason(base + gone);
      reasoner.retract(quads(gone), "complete", options);
      assertEquals(closureKeys(reasoner), closureKeys(reason(rest)));
    }
  }
});

Deno.test("distinct literal values of a functional property derive no differentFrom between subjects", () => {
  const lines = ["ex:id a owl:FunctionalProperty ."];
  for (let i = 0; i < 40; i++) lines.push(`ex:s${i} ex:id "v${i}" .`);
  const reasoner = reason(lines.join("\n"));
  const different = [...reasoner.closure("complete")].filter((q) =>
    q.predicate.value === `${OWL}differentFrom` &&
    q.subject.value.startsWith(EX)
  );
  assertEquals(different.length, 0);
});

Deno.test("subjects with different literal values of a functional property cannot be the same", () => {
  const reasoner = reason(`
ex:id a owl:FunctionalProperty .
ex:a ex:id "1" . ex:b ex:id "2" .
ex:a owl:sameAs ex:b .
`);
  assert(reasoner.inconsistencies().some((i) => i.rule === "eq-diff1"));
});

Deno.test("an inverse-functional merge of subjects with different literal values is inconsistent", () => {
  const reasoner = reason(`
ex:id a owl:FunctionalProperty .
ex:k a owl:InverseFunctionalProperty .
ex:a ex:id "1" ; ex:k ex:z . ex:b ex:id "2" ; ex:k ex:z .
`);
  assert(reasoner.inconsistencies().some((i) => i.rule === "eq-diff1"));
});

// Named graphs.

const graph = (name: string) => dataFactory.namedNode(EX + name);
const RDFS_SUBCLASS = "http://www.w3.org/2000/01/rdf-schema#subClassOf";

function inGraph(g: ReturnType<typeof graph>, turtle: string): Quad[] {
  return quads(turtle).map((q) =>
    dataFactory.quad(q.subject, q.predicate, q.object, g)
  );
}

/** listed is the graph of every closure quad for the triple, sorted. */
function listed(r: Reasoner, s: string, p: string, o: string): string[] {
  const term = (name: string) => name.includes(":") ? iri(name) : ex(name);
  return [...r.closure("complete")]
    .filter((q) =>
      q.subject.equals(term(s)) && q.predicate.equals(term(p)) &&
      q.object.equals(term(o))
    )
    .map((q) =>
      q.graph.termType === "DefaultGraph"
        ? "default"
        : q.graph.equals(DERIVED_GRAPH)
        ? "derived"
        : q.graph.value.replace(EX, "")
    )
    .sort();
}

function twoGraphs(options?: ReasonerOptions): Reasoner {
  const r = new Reasoner(options);
  r.add(inGraph(graph("schema"), "ex:Student rdfs:subClassOf ex:Person ."));
  r.add(inGraph(
    graph("data"),
    "ex:alice a ex:Student . ex:likes a owl:SymmetricProperty . ex:alice ex:likes ex:bob .",
  ));
  r.run();
  return r;
}

Deno.test("per-graph: a triple from one graph's premises stays in that graph", () => {
  const r = twoGraphs();
  assertEquals(listed(r, "bob", "likes", "alice"), ["data"]);
  assertEquals(listed(r, "alice", "likes", "bob"), ["data"]);
  assertEquals(listed(r, "Student", RDFS_SUBCLASS, "Person"), ["schema"]);
});

Deno.test("per-graph: a cross-graph consequence goes in the derived graph", () => {
  const r = twoGraphs();
  assertEquals(listed(r, "alice", RDF_TYPE, "Person"), ["derived"]);
  assert(r.has(ex("alice"), iri(RDF_TYPE), ex("Person")));
  assert(r.has(ex("alice"), iri(RDF_TYPE), ex("Person"), DERIVED_GRAPH));
  assertFalse(r.has(ex("alice"), iri(RDF_TYPE), ex("Person"), graph("data")));
  assert(r.has(ex("alice"), iri(RDF_TYPE), ex("Student"), graph("data")));
});

Deno.test("union: every graph is one closure, listed in the default graph", () => {
  const r = twoGraphs({ graphs: "union" });
  assertEquals(listed(r, "alice", RDF_TYPE, "Person"), ["default"]);
  assertEquals(listed(r, "bob", "likes", "alice"), ["default"]);
  assert(
    r.has(ex("alice"), iri(RDF_TYPE), ex("Person"), dataFactory.defaultGraph()),
  );
  assertFalse(r.has(ex("alice"), iri(RDF_TYPE), ex("Person"), graph("data")));
});

Deno.test("default graph only: both modes list everything in the default graph", () => {
  for (const graphs of ["per-graph", "union"] as const) {
    const r = new Reasoner({ graphs });
    r.add(
      quads("ex:Student rdfs:subClassOf ex:Person . ex:alice a ex:Student ."),
    );
    r.run();
    assertEquals(listed(r, "alice", RDF_TYPE, "Person"), ["default"]);
    assert([...r.closure()].every((q) => q.graph.termType === "DefaultGraph"));
  }
});

Deno.test("per-graph: a triple asserted in two graphs is listed in both", () => {
  const r = new Reasoner();
  for (const name of ["a", "b"]) {
    r.add(inGraph(graph(name), "ex:alice a ex:Student ."));
  }
  r.run();
  assertEquals(listed(r, "alice", RDF_TYPE, "Student"), ["a", "b"]);
});

Deno.test("retract: a triple asserted in another graph stays entailed", () => {
  const r = new Reasoner();
  const a = inGraph(graph("a"), "ex:alice a ex:Student .");
  r.add(a);
  r.add(inGraph(graph("b"), "ex:alice a ex:Student ."));
  r.add(inGraph(graph("b"), "ex:Student rdfs:subClassOf ex:Person ."));
  r.run();
  const removed = r.retract(a);
  assertEquals(
    removed.map((q) => q.graph.value.replace(EX, "")).sort(),
    ["a"],
  );
  assert(r.has(ex("alice"), iri(RDF_TYPE), ex("Person")));
  assertEquals(listed(r, "alice", RDF_TYPE, "Person"), ["b"]);
});

Deno.test("retract: dropping the schema graph's triple removes the derived quad", () => {
  const r = twoGraphs();
  const removed = r.retract(
    inGraph(graph("schema"), "ex:Student rdfs:subClassOf ex:Person ."),
    "application",
  );
  assert(
    removed.some((q) =>
      q.object.equals(ex("Person")) && q.graph.equals(DERIVED_GRAPH)
    ),
  );
  assertFalse(r.has(ex("alice"), iri(RDF_TYPE), ex("Person")));
});

Deno.test("extend: new quads carry their graph", () => {
  const r = twoGraphs();
  const added = r.extend(
    inGraph(graph("data"), "ex:carol a ex:Student ."),
    "application",
  );
  const byObject = (name: string) =>
    added.filter((q) => q.object.equals(ex(name))).map((q) =>
      q.graph.equals(DERIVED_GRAPH) ? "derived" : q.graph.value.replace(EX, "")
    );
  assertEquals(byObject("Student"), ["data"]);
  assertEquals(byObject("Person"), ["derived"]);
});

Deno.test("inconsistencies name the graph, or the derived graph", () => {
  const r = new Reasoner();
  r.add(inGraph(graph("one"), "ex:x a ex:A ."));
  r.add(inGraph(graph("two"), "ex:A owl:disjointWith ex:B ."));
  r.add(inGraph(graph("three"), "ex:x a ex:B ."));
  r.add(
    inGraph(
      graph("four"),
      "ex:c owl:sameAs ex:d . ex:c owl:differentFrom ex:d .",
    ),
  );
  r.run();
  const reports = r.inconsistencies().map((i) =>
    `${i.rule}@${
      i.graph.equals(DERIVED_GRAPH) ? "derived" : i.graph.value.replace(EX, "")
    }`
  ).sort();
  // cls-com fires alongside cax-dw, so only these two rules are compared.
  assertEquals(
    [...new Set(reports)].filter((x) => /^(cax-dw|eq-diff1)@/.test(x)),
    ["cax-dw@derived", "eq-diff1@four"],
  );
});
