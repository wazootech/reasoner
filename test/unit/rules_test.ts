// One minimal case per rule of the OWL 2 RL/RDF rule tables (equality,
// property, class, class axiom, schema and datatype rules). A case either
// lists triples the closure must contain or names the rule an inconsistency
// must report. The engine's own helper rules are exercised through these.
import { assert, assertFalse } from "@std/assert";
import { parseTurtleQuads } from "@wazoo/sparql-engine/parser";
import { dataFactory } from "@wazoo/sparql-engine/term";
import { Reasoner } from "@/mod.ts";

const PREFIXES = `@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .
@prefix ex: <https://reasoner.example/> .
`;
const ZERO = `"0"^^xsd:nonNegativeInteger`;
const ONE = `"1"^^xsd:nonNegativeInteger`;

interface Case {
  /** premise is Turtle; the prefixes above are available. */
  premise: string;
  /** entails is Turtle without blank nodes: every triple must be in the closure. */
  entails?: string;
  /** inconsistent is the rule an inconsistency report must name. */
  inconsistent?: string;
}

const CASES: Record<string, Case> = {
  // Equality
  "eq-sym": {
    premise: `ex:a owl:sameAs ex:b .`,
    entails: `ex:b owl:sameAs ex:a .`,
  },
  "eq-trans": {
    premise: `ex:a owl:sameAs ex:b . ex:b owl:sameAs ex:c .`,
    entails: `ex:a owl:sameAs ex:c .`,
  },
  "eq-rep-s": {
    premise: `ex:a owl:sameAs ex:b . ex:a ex:p ex:o .`,
    entails: `ex:b ex:p ex:o .`,
  },
  "eq-rep-p": {
    premise: `ex:p owl:sameAs ex:q . ex:a ex:p ex:o .`,
    entails: `ex:a ex:q ex:o .`,
  },
  "eq-rep-o": {
    premise: `ex:o owl:sameAs ex:o2 . ex:a ex:p ex:o .`,
    entails: `ex:a ex:p ex:o2 .`,
  },
  "eq-diff1": {
    premise: `ex:a owl:sameAs ex:b . ex:a owl:differentFrom ex:b .`,
    inconsistent: "eq-diff1",
  },
  "eq-diff2": {
    premise:
      `[] a owl:AllDifferent ; owl:members (ex:a ex:b) . ex:a owl:sameAs ex:b .`,
    inconsistent: "eq-diff2",
  },
  "eq-diff3": {
    premise:
      `[] a owl:AllDifferent ; owl:distinctMembers (ex:a ex:b) . ex:a owl:sameAs ex:b .`,
    inconsistent: "eq-diff3",
  },
  // Properties
  "prp-dom": {
    premise: `ex:p rdfs:domain ex:C . ex:x ex:p ex:y .`,
    entails: `ex:x a ex:C .`,
  },
  "prp-rng": {
    premise: `ex:p rdfs:range ex:C . ex:x ex:p ex:y .`,
    entails: `ex:y a ex:C .`,
  },
  "prp-fp": {
    premise: `ex:p a owl:FunctionalProperty . ex:x ex:p ex:y1, ex:y2 .`,
    entails: `ex:y1 owl:sameAs ex:y2 .`,
  },
  "prp-ifp": {
    premise:
      `ex:p a owl:InverseFunctionalProperty . ex:x1 ex:p ex:y . ex:x2 ex:p ex:y .`,
    entails: `ex:x1 owl:sameAs ex:x2 .`,
  },
  "prp-irp": {
    premise: `ex:p a owl:IrreflexiveProperty . ex:x ex:p ex:x .`,
    inconsistent: "prp-irp",
  },
  "prp-symp": {
    premise: `ex:p a owl:SymmetricProperty . ex:x ex:p ex:y .`,
    entails: `ex:y ex:p ex:x .`,
  },
  "prp-asyp": {
    premise:
      `ex:p a owl:AsymmetricProperty . ex:x ex:p ex:y . ex:y ex:p ex:x .`,
    inconsistent: "prp-asyp",
  },
  "prp-trp": {
    premise:
      `ex:p a owl:TransitiveProperty . ex:x ex:p ex:y . ex:y ex:p ex:z .`,
    entails: `ex:x ex:p ex:z .`,
  },
  "prp-spo1": {
    premise: `ex:p1 rdfs:subPropertyOf ex:p2 . ex:x ex:p1 ex:y .`,
    entails: `ex:x ex:p2 ex:y .`,
  },
  "prp-spo2": {
    premise:
      `ex:p owl:propertyChainAxiom (ex:p1 ex:p2) . ex:x ex:p1 ex:y . ex:y ex:p2 ex:z .`,
    entails: `ex:x ex:p ex:z .`,
  },
  "prp-eqp1": {
    premise: `ex:p1 owl:equivalentProperty ex:p2 . ex:x ex:p1 ex:y .`,
    entails: `ex:x ex:p2 ex:y .`,
  },
  "prp-eqp2": {
    premise: `ex:p1 owl:equivalentProperty ex:p2 . ex:x ex:p2 ex:y .`,
    entails: `ex:x ex:p1 ex:y .`,
  },
  "prp-pdw": {
    premise:
      `ex:p1 owl:propertyDisjointWith ex:p2 . ex:x ex:p1 ex:y . ex:x ex:p2 ex:y .`,
    inconsistent: "prp-pdw",
  },
  "prp-adp": {
    premise:
      `[] a owl:AllDisjointProperties ; owl:members (ex:p1 ex:p2) . ex:x ex:p1 ex:y . ex:x ex:p2 ex:y .`,
    inconsistent: "prp-adp",
  },
  "prp-inv1": {
    premise: `ex:p1 owl:inverseOf ex:p2 . ex:x ex:p1 ex:y .`,
    entails: `ex:y ex:p2 ex:x .`,
  },
  "prp-inv2": {
    premise: `ex:p1 owl:inverseOf ex:p2 . ex:x ex:p2 ex:y .`,
    entails: `ex:y ex:p1 ex:x .`,
  },
  "prp-key": {
    premise:
      `ex:C owl:hasKey (ex:k) . ex:x a ex:C ; ex:k ex:v . ex:y a ex:C ; ex:k ex:v .`,
    entails: `ex:x owl:sameAs ex:y .`,
  },
  "prp-npa1": {
    premise:
      `[] a owl:NegativePropertyAssertion ; owl:sourceIndividual ex:i1 ; owl:assertionProperty ex:p ; owl:targetIndividual ex:i2 . ex:i1 ex:p ex:i2 .`,
    inconsistent: "prp-npa1",
  },
  "prp-npa2": {
    premise:
      `[] a owl:NegativePropertyAssertion ; owl:sourceIndividual ex:i ; owl:assertionProperty ex:p ; owl:targetValue "v" . ex:i ex:p "v" .`,
    inconsistent: "prp-npa2",
  },
  // Classes
  "cls-thing": {
    premise: `ex:a ex:p ex:b .`,
    entails: `owl:Thing a owl:Class .`,
  },
  "cls-nothing1": {
    premise: `ex:a ex:p ex:b .`,
    entails: `owl:Nothing a owl:Class .`,
  },
  "cls-nothing2": {
    premise: `ex:x a owl:Nothing .`,
    inconsistent: "cls-nothing2",
  },
  "cls-int1": {
    premise: `ex:C owl:intersectionOf (ex:C1 ex:C2) . ex:x a ex:C1, ex:C2 .`,
    entails: `ex:x a ex:C .`,
  },
  "cls-int2": {
    premise: `ex:C owl:intersectionOf (ex:C1 ex:C2) . ex:x a ex:C .`,
    entails: `ex:x a ex:C1, ex:C2 .`,
  },
  "cls-uni": {
    premise: `ex:C owl:unionOf (ex:C1 ex:C2) . ex:x a ex:C2 .`,
    entails: `ex:x a ex:C .`,
  },
  "cls-com": {
    premise: `ex:C1 owl:complementOf ex:C2 . ex:x a ex:C1, ex:C2 .`,
    inconsistent: "cls-com",
  },
  "cls-svf1": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:someValuesFrom ex:C . ex:u ex:p ex:v . ex:v a ex:C .`,
    entails: `ex:u a ex:R .`,
  },
  "cls-svf2": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:someValuesFrom owl:Thing . ex:u ex:p ex:v .`,
    entails: `ex:u a ex:R .`,
  },
  "cls-avf": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:allValuesFrom ex:C . ex:u a ex:R ; ex:p ex:v .`,
    entails: `ex:v a ex:C .`,
  },
  "cls-hv1": {
    premise: `ex:R owl:onProperty ex:p ; owl:hasValue ex:y . ex:u a ex:R .`,
    entails: `ex:u ex:p ex:y .`,
  },
  "cls-hv2": {
    premise: `ex:R owl:onProperty ex:p ; owl:hasValue ex:y . ex:u ex:p ex:y .`,
    entails: `ex:u a ex:R .`,
  },
  "cls-maxc1": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:maxCardinality ${ZERO} . ex:u a ex:R ; ex:p ex:y .`,
    inconsistent: "cls-maxc1",
  },
  "cls-maxc2": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:maxCardinality ${ONE} . ex:u a ex:R ; ex:p ex:y1, ex:y2 .`,
    entails: `ex:y1 owl:sameAs ex:y2 .`,
  },
  "cls-maxqc1": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:maxQualifiedCardinality ${ZERO} ; owl:onClass ex:C . ex:u a ex:R ; ex:p ex:y . ex:y a ex:C .`,
    inconsistent: "cls-maxqc1",
  },
  "cls-maxqc2": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:maxQualifiedCardinality ${ZERO} ; owl:onClass owl:Thing . ex:u a ex:R ; ex:p ex:y .`,
    inconsistent: "cls-maxqc2",
  },
  "cls-maxqc3": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:maxQualifiedCardinality ${ONE} ; owl:onClass ex:C . ex:u a ex:R ; ex:p ex:y1, ex:y2 . ex:y1 a ex:C . ex:y2 a ex:C .`,
    entails: `ex:y1 owl:sameAs ex:y2 .`,
  },
  "cls-maxqc4": {
    premise:
      `ex:R owl:onProperty ex:p ; owl:maxQualifiedCardinality ${ONE} ; owl:onClass owl:Thing . ex:u a ex:R ; ex:p ex:y1, ex:y2 .`,
    entails: `ex:y1 owl:sameAs ex:y2 .`,
  },
  "cls-oo": {
    premise: `ex:C owl:oneOf (ex:a ex:b) .`,
    entails: `ex:a a ex:C . ex:b a ex:C .`,
  },
  // Class axioms
  "cax-sco": {
    premise: `ex:C1 rdfs:subClassOf ex:C2 . ex:x a ex:C1 .`,
    entails: `ex:x a ex:C2 .`,
  },
  "cax-eqc1": {
    premise: `ex:C1 owl:equivalentClass ex:C2 . ex:x a ex:C1 .`,
    entails: `ex:x a ex:C2 .`,
  },
  "cax-eqc2": {
    premise: `ex:C1 owl:equivalentClass ex:C2 . ex:x a ex:C2 .`,
    entails: `ex:x a ex:C1 .`,
  },
  "cax-dw": {
    premise: `ex:C1 owl:disjointWith ex:C2 . ex:x a ex:C1, ex:C2 .`,
    inconsistent: "cax-dw",
  },
  "cax-adc": {
    premise:
      `[] a owl:AllDisjointClasses ; owl:members (ex:C1 ex:C2) . ex:x a ex:C1, ex:C2 .`,
    inconsistent: "cax-adc",
  },
  // Schema vocabulary
  "scm-cls": {
    premise: `ex:C a owl:Class .`,
    entails:
      `ex:C rdfs:subClassOf ex:C, owl:Thing . ex:C owl:equivalentClass ex:C . owl:Nothing rdfs:subClassOf ex:C .`,
  },
  "scm-sco": {
    premise: `ex:C1 rdfs:subClassOf ex:C2 . ex:C2 rdfs:subClassOf ex:C3 .`,
    entails: `ex:C1 rdfs:subClassOf ex:C3 .`,
  },
  "scm-eqc1": {
    premise: `ex:C1 owl:equivalentClass ex:C2 .`,
    entails: `ex:C1 rdfs:subClassOf ex:C2 . ex:C2 rdfs:subClassOf ex:C1 .`,
  },
  "scm-eqc2": {
    premise: `ex:C1 rdfs:subClassOf ex:C2 . ex:C2 rdfs:subClassOf ex:C1 .`,
    entails: `ex:C1 owl:equivalentClass ex:C2 .`,
  },
  "scm-op": {
    premise: `ex:p a owl:ObjectProperty .`,
    entails:
      `ex:p rdfs:subPropertyOf ex:p . ex:p owl:equivalentProperty ex:p .`,
  },
  "scm-dp": {
    premise: `ex:p a owl:DatatypeProperty .`,
    entails:
      `ex:p rdfs:subPropertyOf ex:p . ex:p owl:equivalentProperty ex:p .`,
  },
  "scm-spo": {
    premise:
      `ex:p1 rdfs:subPropertyOf ex:p2 . ex:p2 rdfs:subPropertyOf ex:p3 .`,
    entails: `ex:p1 rdfs:subPropertyOf ex:p3 .`,
  },
  "scm-eqp1": {
    premise: `ex:p1 owl:equivalentProperty ex:p2 .`,
    entails:
      `ex:p1 rdfs:subPropertyOf ex:p2 . ex:p2 rdfs:subPropertyOf ex:p1 .`,
  },
  "scm-eqp2": {
    premise:
      `ex:p1 rdfs:subPropertyOf ex:p2 . ex:p2 rdfs:subPropertyOf ex:p1 .`,
    entails: `ex:p1 owl:equivalentProperty ex:p2 .`,
  },
  "scm-dom1": {
    premise: `ex:p rdfs:domain ex:C1 . ex:C1 rdfs:subClassOf ex:C2 .`,
    entails: `ex:p rdfs:domain ex:C2 .`,
  },
  "scm-dom2": {
    premise: `ex:p2 rdfs:domain ex:C . ex:p1 rdfs:subPropertyOf ex:p2 .`,
    entails: `ex:p1 rdfs:domain ex:C .`,
  },
  "scm-rng1": {
    premise: `ex:p rdfs:range ex:C1 . ex:C1 rdfs:subClassOf ex:C2 .`,
    entails: `ex:p rdfs:range ex:C2 .`,
  },
  "scm-rng2": {
    premise: `ex:p2 rdfs:range ex:C . ex:p1 rdfs:subPropertyOf ex:p2 .`,
    entails: `ex:p1 rdfs:range ex:C .`,
  },
  "scm-hv": {
    premise:
      `ex:R1 owl:onProperty ex:p1 ; owl:hasValue ex:i . ex:R2 owl:onProperty ex:p2 ; owl:hasValue ex:i . ex:p1 rdfs:subPropertyOf ex:p2 .`,
    entails: `ex:R1 rdfs:subClassOf ex:R2 .`,
  },
  "scm-svf1": {
    premise:
      `ex:R1 owl:onProperty ex:p ; owl:someValuesFrom ex:C1 . ex:R2 owl:onProperty ex:p ; owl:someValuesFrom ex:C2 . ex:C1 rdfs:subClassOf ex:C2 .`,
    entails: `ex:R1 rdfs:subClassOf ex:R2 .`,
  },
  "scm-svf2": {
    premise:
      `ex:R1 owl:onProperty ex:p1 ; owl:someValuesFrom ex:C . ex:R2 owl:onProperty ex:p2 ; owl:someValuesFrom ex:C . ex:p1 rdfs:subPropertyOf ex:p2 .`,
    entails: `ex:R1 rdfs:subClassOf ex:R2 .`,
  },
  "scm-avf1": {
    premise:
      `ex:R1 owl:onProperty ex:p ; owl:allValuesFrom ex:C1 . ex:R2 owl:onProperty ex:p ; owl:allValuesFrom ex:C2 . ex:C1 rdfs:subClassOf ex:C2 .`,
    entails: `ex:R1 rdfs:subClassOf ex:R2 .`,
  },
  "scm-avf2": {
    premise:
      `ex:R1 owl:onProperty ex:p1 ; owl:allValuesFrom ex:C . ex:R2 owl:onProperty ex:p2 ; owl:allValuesFrom ex:C . ex:p1 rdfs:subPropertyOf ex:p2 .`,
    entails: `ex:R2 rdfs:subClassOf ex:R1 .`,
  },
  "scm-int": {
    premise: `ex:C owl:intersectionOf (ex:C1 ex:C2) .`,
    entails: `ex:C rdfs:subClassOf ex:C1, ex:C2 .`,
  },
  "scm-uni": {
    premise: `ex:C owl:unionOf (ex:C1 ex:C2) .`,
    entails: `ex:C1 rdfs:subClassOf ex:C . ex:C2 rdfs:subClassOf ex:C .`,
  },
};

function closureOf(premise: string): Reasoner {
  const reasoner = new Reasoner();
  reasoner.add(parseTurtleQuads(PREFIXES + premise));
  reasoner.run();
  return reasoner;
}

for (const [rule, c] of Object.entries(CASES)) {
  Deno.test(`rule ${rule}`, () => {
    const reasoner = closureOf(c.premise);
    if (c.entails !== undefined) {
      for (const q of parseTurtleQuads(PREFIXES + c.entails)) {
        assert(
          reasoner.has(q.subject, q.predicate, q.object),
          `${rule}: missing ${q.subject.value} ${q.predicate.value} ${q.object.value}`,
        );
      }
    }
    if (c.inconsistent !== undefined) {
      assert(
        reasoner.inconsistencies().some((i) => i.rule === c.inconsistent),
        `${rule}: no ${c.inconsistent} among ${
          JSON.stringify(reasoner.inconsistencies().map((i) => i.rule))
        }`,
      );
    }
  });
}

// Datatype rules name literals, which Turtle cannot put in subject position.
const XSD = "http://www.w3.org/2001/XMLSchema#";
const lit = (value: string, datatype: string) =>
  dataFactory.literal(value, dataFactory.namedNode(XSD + datatype));
const named = (iri: string) => dataFactory.namedNode(iri);
const RDF_TYPE = named("http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
const OWL = "http://www.w3.org/2002/07/owl#";

Deno.test("rule dt-type1: the supported datatypes are datatypes", () => {
  const reasoner = closureOf(`ex:a ex:p ex:b .`);
  assert(
    reasoner.has(
      named(XSD + "integer"),
      RDF_TYPE,
      named("http://www.w3.org/2000/01/rdf-schema#Datatype"),
    ),
  );
});

Deno.test("rule dt-type2: a literal is a member of its datatype", () => {
  const reasoner = closureOf(`ex:a ex:p "1"^^xsd:integer .`);
  assert(reasoner.has(lit("1", "integer"), RDF_TYPE, named(XSD + "integer")));
  assert(reasoner.has(lit("1", "integer"), RDF_TYPE, named(XSD + "decimal")));
});

Deno.test("rule eq-ref is not materialized, as documented in rules.ts", () => {
  const reasoner = closureOf(`ex:a ex:p ex:b .`);
  assertFalse(
    reasoner.has(
      named("https://reasoner.example/a"),
      named(OWL + "sameAs"),
      named("https://reasoner.example/a"),
    ),
  );
});

const SAME_AS = named(OWL + "sameAs");
const EX_B = named("https://reasoner.example/b");
const EX_P = named("https://reasoner.example/p");

Deno.test("rule dt-eq: equal decimal-space values of different spellings are one class", () => {
  const reasoner = closureOf(
    `ex:a ex:p "1"^^xsd:integer . ex:b ex:p "1.0"^^xsd:decimal .
ex:c ex:p "01"^^xsd:int . ex:d ex:p "+1.00"^^xsd:decimal .`,
  );
  const one = lit("1", "integer");
  for (
    const [v, d] of [["1.0", "decimal"], ["01", "int"], ["+1.00", "decimal"]]
  ) {
    assert(reasoner.has(one, SAME_AS, lit(v!, d!)), v);
  }
  // eq-rep-o: the subjects now hold every equal spelling.
  assert(reasoner.has(EX_B, EX_P, one));
  // The value spaces agree on types: "1.0"^^xsd:decimal is an xsd:integer value.
  assertFalse(reasoner.inconsistencies().length > 0);
  assert(reasoner.has(lit("1.0", "decimal"), RDF_TYPE, named(XSD + "integer")));
});

Deno.test("rule dt-eq: booleans true and 1 are the same value", () => {
  const reasoner = closureOf(
    `ex:a ex:p "true"^^xsd:boolean . ex:b ex:p "1"^^xsd:boolean .
ex:c ex:p "false"^^xsd:boolean . ex:d ex:p "0"^^xsd:boolean .`,
  );
  assert(reasoner.has(lit("true", "boolean"), SAME_AS, lit("1", "boolean")));
  assert(reasoner.has(lit("false", "boolean"), SAME_AS, lit("0", "boolean")));
  assertFalse(
    reasoner.has(lit("true", "boolean"), SAME_AS, lit("0", "boolean")),
  );
});

Deno.test("rule dt-eq: different values, other datatypes, ill-typed and NaN stay apart", () => {
  const reasoner = closureOf(
    `ex:a ex:p "1"^^xsd:integer . ex:a ex:p "2"^^xsd:integer .
ex:a ex:p "1" . ex:a ex:p "01" . ex:a ex:p "1"^^xsd:boolean .
ex:a ex:p "2026-01-01T00:00:00Z"^^xsd:dateTime . ex:a ex:p "2026-01-01T01:00:00+01:00"^^xsd:dateTime .
ex:a ex:p "x"^^xsd:integer . ex:a ex:p "NaN"^^xsd:double . ex:a ex:p "NaN"^^xsd:float .
ex:a ex:p "0"^^xsd:double . ex:a ex:p "-0"^^xsd:double . ex:a ex:p "1.1"^^xsd:decimal . ex:a ex:p "1"^^xsd:double .`,
  );
  const no = (a: string, b: string) =>
    assertFalse(
      reasoner.has(
        lit(a.split("|")[0]!, a.split("|")[1]!),
        SAME_AS,
        lit(b.split("|")[0]!, b.split("|")[1]!),
      ),
      a + " " + b,
    );
  no("1|integer", "2|integer");
  no("1|integer", "1|boolean");
  no("NaN|double", "NaN|float");
  no("0|double", "-0|double");
  no("1|integer", "1.1|decimal");
  no("1|integer", "1|double");
  assertFalse(
    reasoner.has(
      lit("2026-01-01T00:00:00Z", "dateTime"),
      SAME_AS,
      lit("2026-01-01T01:00:00+01:00", "dateTime"),
    ),
  );
});

Deno.test("rule dt-eq: floats equal floats and doubles equal doubles, never across spaces", () => {
  const reasoner = closureOf(
    `ex:a ex:p "1.1"^^xsd:double , "1.10"^^xsd:double , "1.1"^^xsd:float , "1.1"^^xsd:decimal .
ex:b ex:p "1E21"^^xsd:double , "1000000000000000000000"^^xsd:double , "1000000000000000000000"^^xsd:integer .
ex:c ex:p "0"^^xsd:float , "+0.0"^^xsd:float , "INF"^^xsd:float , "+INF"^^xsd:float .`,
  );
  assert(reasoner.has(lit("1.1", "double"), SAME_AS, lit("1.10", "double")));
  assert(
    reasoner.has(
      lit("1E21", "double"),
      SAME_AS,
      lit("1000000000000000000000", "double"),
    ),
  );
  assert(reasoner.has(lit("0", "float"), SAME_AS, lit("+0.0", "float")));
  assert(reasoner.has(lit("INF", "float"), SAME_AS, lit("+INF", "float")));
  assertFalse(reasoner.has(lit("1.1", "double"), SAME_AS, lit("1.1", "float")));
  assertFalse(
    reasoner.has(lit("1.1", "double"), SAME_AS, lit("1.1", "decimal")),
  );
  assertFalse(
    reasoner.has(
      lit("1E21", "double"),
      SAME_AS,
      lit("1000000000000000000000", "integer"),
    ),
  );
  assertFalse(reasoner.has(lit("0", "float"), SAME_AS, lit("INF", "float")));
});

Deno.test("rule dt-eq: a functional property with equal-valued spellings is consistent", () => {
  const reasoner = closureOf(
    `ex:p a owl:FunctionalProperty . ex:a ex:p "1"^^xsd:integer , "1.0"^^xsd:decimal .`,
  );
  assertFalse(reasoner.inconsistencies().length > 0);
});

Deno.test("rule dt-eq: owl:differentFrom between equal values is inconsistent", () => {
  const reasoner = closureOf(
    `ex:a ex:p "1"^^xsd:integer . ex:b ex:p "1.0"^^xsd:decimal .`,
  );
  reasoner.extend([
    dataFactory.quad(
      lit("1", "integer"),
      named(OWL + "differentFrom"),
      lit("1.0", "decimal"),
    ),
  ], "application");
  assert(reasoner.inconsistencies().some((i) => i.rule === "eq-diff1"));
});

Deno.test("rule dt-eq: hasKey merges individuals whose keys are equal values", () => {
  const reasoner = closureOf(
    `ex:C owl:hasKey (ex:id) .
ex:a a ex:C ; ex:id "1"^^xsd:integer . ex:b a ex:C ; ex:id "1.0"^^xsd:decimal .
ex:c a ex:C ; ex:id "2"^^xsd:integer .`,
  );
  assert(
    reasoner.has(
      named("https://reasoner.example/a"),
      SAME_AS,
      named("https://reasoner.example/b"),
    ),
  );
  assertFalse(
    reasoner.has(
      named("https://reasoner.example/a"),
      SAME_AS,
      named("https://reasoner.example/c"),
    ),
  );
});

Deno.test("rule dt-eq: a value met later joins its class (extend and retract)", () => {
  const reasoner = closureOf(`ex:a ex:p "1"^^xsd:integer .`);
  const parse = (turtle: string) => parseTurtleQuads(PREFIXES + turtle);
  assertFalse(
    reasoner.has(lit("1", "integer"), SAME_AS, lit("1.0", "decimal")),
  );
  const added = parse(`ex:b ex:p "1.0"^^xsd:decimal .`);
  reasoner.extend(added, "application");
  assert(reasoner.has(lit("1", "integer"), SAME_AS, lit("1.0", "decimal")));
  reasoner.retract(added, "application");
  assertFalse(
    reasoner.has(lit("1", "integer"), SAME_AS, lit("1.0", "decimal")),
  );
});

Deno.test("rule dt-diff: different values are different", () => {
  const reasoner = closureOf(
    `ex:a ex:p "1"^^xsd:integer . ex:a ex:p "2"^^xsd:integer .
ex:p a owl:FunctionalProperty .`,
  );
  assert(
    reasoner.has(
      lit("1", "integer"),
      named(OWL + "differentFrom"),
      lit("2", "integer"),
    ),
  );
  assert(reasoner.inconsistencies().some((i) => i.rule === "eq-diff1"));
});

Deno.test("rule dt-not-type: an ill-typed literal is inconsistent", () => {
  const reasoner = closureOf(`ex:a ex:p "x"^^xsd:integer .`);
  assert(reasoner.inconsistencies().some((i) => i.rule === "dt-not-type"));
});

Deno.test("rule prp-trp-chain: a transitive property is its own (p p) chain", () => {
  const r = closureOf(`ex:p a owl:TransitiveProperty .`);
  const has = (view: "complete" | "application") =>
    [...r.closure(view)].filter((q) =>
      q.predicate.value === "http://www.w3.org/2002/07/owl#propertyChainAxiom"
    ).length;
  assert(has("complete") === 1);
  // The skolem list is bookkeeping: the application view does not list it.
  assert(has("application") === 0);
});
