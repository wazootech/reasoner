import { assert, assertEquals, assertFalse } from "@std/assert";
import { parseTurtleQuads } from "@wazoo/sparql-engine/parser";
import { dataFactory } from "@wazoo/sparql-engine/term";
import type { Quad } from "@rdfjs/types";
import { Reasoner } from "@/mod.ts";

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
