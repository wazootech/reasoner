/**
 * The OWL 2 RL/RDF rules (W3C OWL 2 Profiles, section 4.3), plus the handful
 * of RDF-Based consequences the Wiki's previous ruleset added for the
 * official conformance tests, each named after the table entry it implements.
 *
 * Three groups are not rules here:
 *
 * - **eq-sym, eq-trans, eq-rep-s/p/o** are the engine's union-find: an
 *   `owl:sameAs` fact merges two terms, and the closure is expanded per class
 *   on output. eq-ref is not materialized, as before.
 * - **dt-eq** is left out: a literal `owl:sameAs` between equal values of
 *   different spellings only ever copied a value onto every subject holding an
 *   equal one (wazootech/wiki#367).
 * - **dt-diff** is not materialized between unrelated literals, because it is
 *   quadratic in the graph's distinct literals. Where a different value
 *   matters to another rule (a functional property with two values, two
 *   different literals in one equality class), that rule compares the values
 *   directly.
 *
 * List-shaped rules (intersections, chains, keys, `AllDifferent`) run over
 * internal relations that walk each RDF list once: `list` marks a list node an
 * axiom points at (and each tail), `member` and `pair` hold its members and
 * its ordered member pairs.
 */
import type { Literal, NamedNode, Term } from "@rdfjs/types";
import { dataFactory, termKey } from "@wazoo/sparql-engine/term";
import {
  isInstanceOf,
  isInvalidFor,
  literalDatatype,
  valuesDiffer,
} from "@/owl2rl/datatypes.ts";
import { OWL, RDF, RDFS, XSD } from "@/owl2rl/vocabulary.ts";
import {
  atom,
  type AtomPattern,
  bind,
  type BuiltinContext,
  filter,
  type Rule,
  type RuleArgument,
  variables,
} from "@/rule.ts";

/** TRIPLE is the relation holding the graph. */
export const TRIPLE = "triple";
/** INCONSISTENCY is the relation holding one row per inconsistency found. */
export const INCONSISTENCY = "inconsistency";

/** RELATIONS declares every relation the ruleset uses, with its arity. */
export const RELATIONS = {
  [TRIPLE]: 3,
  [INCONSISTENCY]: 6,
  list: 1,
  member: 2,
  pair: 3,
  chainList: 1,
  chainPath: 3,
  intersectionList: 1,
  allTypes: 2,
  keyContext: 2,
  sameValues: 4,
  literal: 1,
  stringClass: 1,
} as const;

/** NONE pads an inconsistency row that names fewer than five terms. */
export const NONE: NamedNode = dataFactory.namedNode(
  "https://wazoo.dev/reasoner/ns#none",
);

/** COMPLEMENT_PREFIX starts the skolem IRI naming the complement of a class. */
export const COMPLEMENT_PREFIX =
  "https://wazoo.dev/.well-known/genid/reasoner/complement/";

const v = variables();
const ZERO = dataFactory.literal("0", XSD.nonNegativeInteger);
const ONE = dataFactory.literal("1", XSD.nonNegativeInteger);

function t(s: RuleArgument, p: RuleArgument, o: RuleArgument): AtomPattern {
  return atom(TRIPLE, s, p, o);
}

function rule(
  name: string,
  body: Rule["body"],
  head: Rule["head"],
): Rule {
  return { name, body, head };
}

/** inconsistent builds the head row that reports rule `name` over `terms`. */
function inconsistent(name: string, ...terms: RuleArgument[]): AtomPattern {
  const padded = [...terms];
  while (padded.length < 5) padded.push(NONE);
  return atom(INCONSISTENCY, dataFactory.literal(name), ...padded);
}

/** literalsOf yields the members of `id`'s class that are literals. */
function* literalsOf(
  id: number,
  context: BuiltinContext,
): Generator<[number, Literal]> {
  for (const member of context.members(context.find(id))) {
    const term = context.term(member);
    if (term.termType === "Literal") yield [member, term];
  }
}

/**
 * isPlainString is `true` for the datatypes the old ruleset typed directly
 * instead of indexing them for value comparison.
 */
function isPlainString(literal: Literal): boolean {
  const datatype = literalDatatype(literal);
  return datatype === XSD.string.value || datatype === RDF.langString.value;
}

const literalMember = bind(
  "literal-member",
  [v.lt],
  [v.m],
  function* (inputs, context) {
    for (const [member, literal] of literalsOf(inputs[0]!, context)) {
      if (!isPlainString(literal)) yield [member];
    }
  },
);

const stringMember = (datatype: NamedNode) =>
  bind(`${datatype.value}-member`, [v.o], [v.lt], function* (inputs, context) {
    for (const [member, literal] of literalsOf(inputs[0]!, context)) {
      if (literalDatatype(literal) === datatype.value) yield [member];
    }
  });

/** someValuesDiffer: some non-string literals of the two classes differ. */
function someValuesDiffer(
  left: number,
  right: number,
  context: BuiltinContext,
  strings: boolean,
): boolean {
  for (const [, a] of literalsOf(left, context)) {
    if (isPlainString(a) !== strings) continue;
    if (strings && literalDatatype(a) !== XSD.string.value) continue;
    for (const [, b] of literalsOf(right, context)) {
      if (isPlainString(b) !== strings) continue;
      if (strings && literalDatatype(b) !== XSD.string.value) continue;
      if (valuesDiffer(a, b)) return true;
    }
  }
  return false;
}

const complementOf = bind(
  "complement",
  [v.c],
  [v.notC],
  (inputs, context) => {
    const named = context.term(context.find(inputs[0]!));
    const iri = COMPLEMENT_PREFIX + encodeURIComponent(termKey(named));
    return [[context.id(dataFactory.namedNode(iri))]];
  },
);

/** complementHead declares `?notC` as the complement class of `c`. */
function complementHead(c: RuleArgument): Rule["head"] {
  return [
    t(v.notC, RDF.type, OWL.Class),
    t(v.notC, OWL.complementOf, c),
  ];
}

const same = filter(
  "same",
  [v.zi, v.zj],
  ([a, b], context) => context.find(a!) === context.find(b!),
);

/** The axiomatic triples: the old ruleset's vocabulary sections 0-2 and 6. */
export const AXIOMS: readonly (readonly [Term, Term, Term])[] = [
  [OWL.sameAs, RDF.type, OWL.ReflexiveProperty],
  [OWL.differentFrom, RDF.type, OWL.SymmetricProperty],
  [OWL.NamedIndividual, RDF.type, OWL.Class],
  [OWL.NamedIndividual, RDFS.subClassOf, OWL.Thing],
  // dt-type1
  ...[
    RDF.PlainLiteral,
    RDF.XMLLiteral,
    RDFS.Literal,
    XSD.decimal,
    XSD.integer,
    XSD.nonNegativeInteger,
    XSD.nonPositiveInteger,
    XSD.positiveInteger,
    XSD.negativeInteger,
    XSD.long,
    XSD.int,
    XSD.short,
    XSD.byte,
    XSD.unsignedLong,
    XSD.unsignedInt,
    XSD.unsignedShort,
    XSD.unsignedByte,
    XSD.float,
    XSD.double,
    XSD.string,
    XSD.normalizedString,
    XSD.token,
    XSD.language,
    XSD.Name,
    XSD.NCName,
    XSD.NMTOKEN,
    XSD.boolean,
    XSD.hexBinary,
    XSD.base64Binary,
    XSD.anyURI,
    XSD.dateTime,
    XSD.dateTimeStamp,
  ].map((datatype) => [datatype, RDF.type, RDFS.Datatype] as const),
  ...([
    [XSD.integer, XSD.decimal],
    [XSD.long, XSD.integer],
    [XSD.int, XSD.long],
    [XSD.short, XSD.int],
    [XSD.byte, XSD.short],
    [XSD.nonPositiveInteger, XSD.integer],
    [XSD.negativeInteger, XSD.nonPositiveInteger],
    [XSD.nonNegativeInteger, XSD.integer],
    [XSD.positiveInteger, XSD.nonNegativeInteger],
    [XSD.unsignedLong, XSD.nonNegativeInteger],
    [XSD.unsignedInt, XSD.unsignedLong],
    [XSD.unsignedShort, XSD.unsignedInt],
    [XSD.unsignedByte, XSD.unsignedShort],
    [XSD.dateTimeStamp, XSD.dateTime],
    [XSD.normalizedString, XSD.string],
    [XSD.token, XSD.normalizedString],
    [XSD.language, XSD.token],
    [XSD.Name, XSD.token],
    [XSD.NCName, XSD.Name],
    [XSD.NMTOKEN, XSD.token],
  ] as const).map(([sub, sup]) => [sub, RDFS.subClassOf, sup] as const),
  // prp-ap
  ...[
    RDFS.label,
    RDFS.comment,
    RDFS.seeAlso,
    RDFS.isDefinedBy,
    OWL.deprecated,
    OWL.versionInfo,
    OWL.priorVersion,
    OWL.backwardCompatibleWith,
    OWL.incompatibleWith,
  ].map((property) => [property, RDF.type, OWL.AnnotationProperty] as const),
  // cls-thing, cls-nothing1
  [OWL.Thing, RDF.type, OWL.Class],
  [OWL.Nothing, RDF.type, OWL.Class],
];

const LIST_AXIOMS = [
  OWL.intersectionOf,
  OWL.unionOf,
  OWL.oneOf,
  OWL.members,
  OWL.distinctMembers,
  OWL.hasKey,
  OWL.propertyChainAxiom,
];

/** listRules maintain the internal list relations. */
const listRules: Rule[] = [
  ...LIST_AXIOMS.map((property) =>
    rule(`list-root ${property.value}`, [t(v.x, property, v.l)], [
      atom("list", v.l),
    ])
  ),
  rule("list-tail", [
    atom("list", v.l),
    t(v.l, RDF.rest, v.tail),
    t(v.tail, RDF.first, v.head),
  ], [atom("list", v.tail)]),
  rule("list-member-first", [atom("list", v.l), t(v.l, RDF.first, v.x)], [
    atom("member", v.l, v.x),
  ]),
  rule("list-member-rest", [
    atom("list", v.l),
    t(v.l, RDF.rest, v.tail),
    atom("member", v.tail, v.x),
  ], [atom("member", v.l, v.x)]),
  rule("list-pair-first", [
    atom("list", v.l),
    t(v.l, RDF.first, v.left),
    t(v.l, RDF.rest, v.tail),
    atom("member", v.tail, v.right),
  ], [atom("pair", v.l, v.left, v.right)]),
  rule("list-pair-rest", [
    atom("list", v.l),
    t(v.l, RDF.rest, v.tail),
    atom("pair", v.tail, v.left, v.right),
  ], [atom("pair", v.l, v.left, v.right)]),
];

const equalityRules: Rule[] = [
  rule("eq-diff1", [t(v.x, OWL.differentFrom, v.x)], [
    inconsistent("eq-diff1", v.x, v.x),
  ]),
  ...[OWL.members, OWL.distinctMembers].map((property, index) =>
    rule(`eq-diff${index + 2}`, [
      t(v.ad, RDF.type, OWL.AllDifferent),
      t(v.ad, property, v.l),
      atom("pair", v.l, v.zi, v.zj),
      same,
    ], [inconsistent(`eq-diff${index + 2}`, v.ad, v.zi, v.zj)])
  ),
  // Two different values in one equality class: the dt-diff consequence the
  // class needs, without comparing every literal in the graph.
  rule("dt-diff-class", [
    t(v.r, OWL.sameAs, v.r),
    filter(
      "different-values",
      [v.r],
      ([r], context) => someValuesDiffer(r!, r!, context, false),
    ),
  ], [t(v.r, OWL.differentFrom, v.r)]),
  // The old ruleset's sameAs-scoped xsd:string difference.
  rule("string-class", [
    t(v.r, OWL.sameAs, v.r),
    filter("has-string", [v.r], ([r], context) => {
      for (const [, literal] of literalsOf(r!, context)) {
        if (literalDatatype(literal) === XSD.string.value) return true;
      }
      return false;
    }),
  ], [atom("stringClass", v.r)]),
  rule("dt-diff-string", [
    atom("stringClass", v.a),
    atom("stringClass", v.b),
    filter(
      "different-strings",
      [v.a, v.b],
      ([a, b], context) => someValuesDiffer(a!, b!, context, true),
    ),
  ], [t(v.a, OWL.differentFrom, v.b)]),
];

const propertyRules: Rule[] = [
  rule("prp-dom", [t(v.p, RDFS.domain, v.c), t(v.x, v.p, v.y)], [
    t(v.x, RDF.type, v.c),
  ]),
  rule("prp-rng", [t(v.p, RDFS.range, v.c), t(v.x, v.p, v.y)], [
    t(v.y, RDF.type, v.c),
  ]),
  rule("prp-fp", [
    t(v.p, RDF.type, OWL.FunctionalProperty),
    t(v.x, v.p, v.y1),
    t(v.x, v.p, v.y2),
  ], [t(v.y1, OWL.sameAs, v.y2)]),
  rule("prp-ifp", [
    t(v.p, RDF.type, OWL.InverseFunctionalProperty),
    t(v.x1, v.p, v.y),
    t(v.x2, v.p, v.y),
  ], [t(v.x1, OWL.sameAs, v.x2)]),
  rule("prp-irp", [
    t(v.p, RDF.type, OWL.IrreflexiveProperty),
    t(v.x, v.p, v.x),
  ], [inconsistent("prp-irp", v.p, v.x)]),
  rule("prp-symp", [
    t(v.p, RDF.type, OWL.SymmetricProperty),
    t(v.x, v.p, v.y),
  ], [t(v.y, v.p, v.x)]),
  rule("prp-asyp", [
    t(v.p, RDF.type, OWL.AsymmetricProperty),
    t(v.x, v.p, v.y),
    t(v.y, v.p, v.x),
  ], [inconsistent("prp-asyp", v.p, v.x, v.y)]),
  rule("prp-trp", [
    t(v.p, RDF.type, OWL.TransitiveProperty),
    t(v.x, v.p, v.y),
    t(v.y, v.p, v.z),
  ], [t(v.x, v.p, v.z)]),
  rule("prp-rp", [
    t(v.p, RDF.type, OWL.ReflexiveProperty),
    t(v.x, RDF.type, OWL.NamedIndividual),
  ], [t(v.x, v.p, v.x)]),
  rule("prp-spo1", [t(v.p1, RDFS.subPropertyOf, v.p2), t(v.x, v.p1, v.y)], [
    t(v.x, v.p2, v.y),
  ]),
  // prp-spo2, for chains of any length.
  rule("chain-root", [t(v.x, OWL.propertyChainAxiom, v.l)], [
    atom("chainList", v.l),
  ]),
  rule("chain-tail", [
    atom("chainList", v.l),
    t(v.l, RDF.rest, v.tail),
    t(v.tail, RDF.first, v.head),
  ], [atom("chainList", v.tail)]),
  rule("chain-last", [
    atom("chainList", v.l),
    t(v.l, RDF.first, v.p),
    t(v.l, RDF.rest, RDF.nil),
    t(v.x, v.p, v.y),
  ], [atom("chainPath", v.l, v.x, v.y)]),
  rule("chain-step", [
    atom("chainList", v.l),
    t(v.l, RDF.first, v.p),
    t(v.l, RDF.rest, v.tail),
    atom("chainPath", v.tail, v.z, v.y),
    t(v.x, v.p, v.z),
  ], [atom("chainPath", v.l, v.x, v.y)]),
  rule("prp-spo2", [
    t(v.p, OWL.propertyChainAxiom, v.l),
    atom("chainPath", v.l, v.x, v.y),
  ], [t(v.x, v.p, v.y)]),
  rule("prp-spo2-transitive", [
    t(v.p, OWL.propertyChainAxiom, v.l),
    t(v.l, RDF.first, v.p),
    t(v.l, RDF.rest, v.tail),
    t(v.tail, RDF.first, v.p),
    t(v.tail, RDF.rest, RDF.nil),
  ], [t(v.p, RDF.type, OWL.TransitiveProperty)]),
  rule("prp-eqp1", [t(v.p1, OWL.equivalentProperty, v.p2), t(v.x, v.p1, v.y)], [
    t(v.x, v.p2, v.y),
  ]),
  rule("prp-eqp2", [t(v.p1, OWL.equivalentProperty, v.p2), t(v.x, v.p2, v.y)], [
    t(v.x, v.p1, v.y),
  ]),
  rule("prp-pdw", [
    t(v.p1, OWL.propertyDisjointWith, v.p2),
    t(v.x, v.p1, v.y),
    t(v.x, v.p2, v.y),
  ], [inconsistent("prp-pdw", v.p1, v.p2, v.x, v.y)]),
  ...disjointPropertyDifferences(
    "prp-pdw",
    [t(v.p1, OWL.propertyDisjointWith, v.p2)],
  ),
  rule("prp-adp", [
    t(v.adp, RDF.type, OWL.AllDisjointProperties),
    t(v.adp, OWL.members, v.l),
    atom("pair", v.l, v.p1, v.p2),
    t(v.u, v.p1, v.w),
    t(v.u, v.p2, v.w),
  ], [inconsistent("prp-adp", v.adp, v.p1, v.p2, v.u, v.w)]),
  ...disjointPropertyDifferences("prp-adp", [
    t(v.adp, RDF.type, OWL.AllDisjointProperties),
    t(v.adp, OWL.members, v.l),
    atom("pair", v.l, v.p1, v.p2),
  ]),
  rule("prp-inv1", [t(v.p1, OWL.inverseOf, v.p2), t(v.x, v.p1, v.y)], [
    t(v.y, v.p2, v.x),
  ]),
  rule("prp-inv2", [t(v.p1, OWL.inverseOf, v.p2), t(v.x, v.p2, v.y)], [
    t(v.y, v.p1, v.x),
  ]),
  // prp-key: keyContext walks each key list with its class, and sameValues
  // holds the pairs of instances that share a value for every key property
  // from that list node to its end.
  rule("key-root", [t(v.c, OWL.hasKey, v.l)], [atom("keyContext", v.l, v.c)]),
  rule("key-tail", [
    atom("keyContext", v.l, v.c),
    t(v.l, RDF.rest, v.tail),
    t(v.tail, RDF.first, v.head),
  ], [atom("keyContext", v.tail, v.c)]),
  rule("key-last", [
    atom("keyContext", v.l, v.c),
    t(v.l, RDF.first, v.p),
    t(v.l, RDF.rest, RDF.nil),
    t(v.x, v.p, v.z),
    t(v.x, RDF.type, v.c),
    t(v.y, v.p, v.z),
    t(v.y, RDF.type, v.c),
  ], [atom("sameValues", v.x, v.y, v.l, v.c)]),
  rule("key-step", [
    atom("keyContext", v.l, v.c),
    t(v.l, RDF.first, v.p),
    t(v.l, RDF.rest, v.tail),
    atom("sameValues", v.x, v.y, v.tail, v.c),
    t(v.x, v.p, v.z),
    t(v.y, v.p, v.z),
  ], [atom("sameValues", v.x, v.y, v.l, v.c)]),
  rule("prp-key", [
    t(v.c, OWL.hasKey, v.l),
    atom("sameValues", v.x, v.y, v.l, v.c),
  ], [t(v.x, OWL.sameAs, v.y)]),
  // Contrapositives of prp-fp and prp-ifp (RDF-Based consequences).
  rule("prp-fp-different", [
    t(v.p, RDF.type, OWL.FunctionalProperty),
    t(v.x1, v.p, v.y1),
    t(v.y1, OWL.differentFrom, v.y2),
    t(v.x2, v.p, v.y2),
  ], [t(v.x1, OWL.differentFrom, v.x2)]),
  rule("prp-fp-different-values", [
    t(v.p, RDF.type, OWL.FunctionalProperty),
    t(v.x1, v.p, v.y1),
    filter(
      "has-value",
      [v.y1],
      ([y], context) => [...literalsOf(y!, context)].length > 0,
    ),
    t(v.x2, v.p, v.y2),
    filter(
      "different-values",
      [v.y1, v.y2],
      ([a, b], context) => someValuesDiffer(a!, b!, context, false),
    ),
  ], [t(v.x1, OWL.differentFrom, v.x2)]),
  rule("prp-ifp-different", [
    t(v.p, RDF.type, OWL.InverseFunctionalProperty),
    t(v.x1, v.p, v.y1),
    t(v.x1, OWL.differentFrom, v.x2),
    t(v.x2, v.p, v.y2),
  ], [t(v.y1, OWL.differentFrom, v.y2)]),
  rule("prp-npa1", [
    t(v.npa, OWL.sourceIndividual, v.i1),
    t(v.npa, OWL.assertionProperty, v.p),
    t(v.npa, OWL.targetIndividual, v.i2),
    t(v.i1, v.p, v.i2),
  ], [inconsistent("prp-npa1", v.npa, v.i1, v.p, v.i2)]),
  rule("prp-npa2", [
    t(v.npa, OWL.sourceIndividual, v.i),
    t(v.npa, OWL.assertionProperty, v.p),
    t(v.npa, OWL.targetValue, v.lt),
    t(v.i, v.p, v.lt),
  ], [inconsistent("prp-npa2", v.npa, v.i, v.p, v.lt)]),
];

/**
 * disjointPropertyDifferences: if disjoint properties relate two subjects to
 * one value, the subjects differ; if they relate one subject to two values,
 * the values differ (both directions of each).
 */
function disjointPropertyDifferences(
  name: string,
  schema: Rule["body"],
): Rule[] {
  return [
    rule(`${name}-subjects`, [
      ...schema,
      t(v.x1, v.p1, v.y),
      t(v.x2, v.p2, v.y),
    ], [t(v.x1, OWL.differentFrom, v.x2), t(v.x2, OWL.differentFrom, v.x1)]),
    rule(`${name}-objects`, [
      ...schema,
      t(v.x, v.p1, v.y1),
      t(v.x, v.p2, v.y2),
    ], [t(v.y1, OWL.differentFrom, v.y2), t(v.y2, OWL.differentFrom, v.y1)]),
  ];
}

const classRules: Rule[] = [
  rule("cls-nothing2", [t(v.x, RDF.type, OWL.Nothing)], [
    inconsistent("cls-nothing2", v.x),
  ]),
  // cls-int1, for intersections of any length.
  rule("intersection-root", [t(v.c, OWL.intersectionOf, v.l)], [
    atom("intersectionList", v.l),
  ]),
  rule("intersection-tail", [
    atom("intersectionList", v.l),
    t(v.l, RDF.rest, v.tail),
    t(v.tail, RDF.first, v.head),
  ], [atom("intersectionList", v.tail)]),
  rule("intersection-last", [
    atom("intersectionList", v.l),
    t(v.l, RDF.first, v.c),
    t(v.l, RDF.rest, RDF.nil),
    t(v.y, RDF.type, v.c),
  ], [atom("allTypes", v.y, v.l)]),
  rule("intersection-step", [
    atom("intersectionList", v.l),
    t(v.l, RDF.first, v.c),
    t(v.l, RDF.rest, v.tail),
    atom("allTypes", v.y, v.tail),
    t(v.y, RDF.type, v.c),
  ], [atom("allTypes", v.y, v.l)]),
  rule("cls-int1", [
    t(v.c, OWL.intersectionOf, v.l),
    atom("allTypes", v.y, v.l),
  ], [t(v.y, RDF.type, v.c)]),
  rule("cls-int2", [
    t(v.c, OWL.intersectionOf, v.l),
    t(v.y, RDF.type, v.c),
    atom("member", v.l, v.ci),
  ], [t(v.y, RDF.type, v.ci)]),
  rule("cls-uni", [
    t(v.c, OWL.unionOf, v.l),
    atom("member", v.l, v.ci),
    t(v.y, RDF.type, v.ci),
  ], [t(v.y, RDF.type, v.c)]),
  rule("cls-com", [
    t(v.c1, OWL.complementOf, v.c2),
    t(v.x, RDF.type, v.c1),
    t(v.x, RDF.type, v.c2),
  ], [inconsistent("cls-com", v.c1, v.c2, v.x)]),
  rule("cls-svf1", [
    t(v.r, OWL.someValuesFrom, v.c),
    t(v.r, OWL.onProperty, v.p),
    t(v.u, v.p, v.w),
    t(v.w, RDF.type, v.c),
  ], [t(v.u, RDF.type, v.r)]),
  rule("cls-svf2", [
    t(v.r, OWL.someValuesFrom, OWL.Thing),
    t(v.r, OWL.onProperty, v.p),
    t(v.u, v.p, v.w),
  ], [t(v.u, RDF.type, v.r)]),
  rule("cls-avf", [
    t(v.r, OWL.allValuesFrom, v.c),
    t(v.r, OWL.onProperty, v.p),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.w),
  ], [t(v.w, RDF.type, v.c)]),
  rule("cls-hv1", [
    t(v.r, OWL.hasValue, v.value),
    t(v.r, OWL.onProperty, v.p),
    t(v.u, RDF.type, v.r),
  ], [t(v.u, v.p, v.value)]),
  rule("cls-hv2", [
    t(v.r, OWL.hasValue, v.value),
    t(v.r, OWL.onProperty, v.p),
    t(v.u, v.p, v.value),
  ], [t(v.u, RDF.type, v.r)]),
  rule("cls-maxc1", [
    t(v.r, OWL.maxCardinality, ZERO),
    t(v.r, OWL.onProperty, v.p),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y),
  ], [inconsistent("cls-maxc1", v.r, v.u, v.p, v.y)]),
  rule("cls-maxc2", [
    t(v.r, OWL.maxCardinality, ONE),
    t(v.r, OWL.onProperty, v.p),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y1),
    t(v.u, v.p, v.y2),
  ], [t(v.y1, OWL.sameAs, v.y2)]),
  rule("cls-maxqc1", [
    t(v.r, OWL.maxQualifiedCardinality, ZERO),
    t(v.r, OWL.onProperty, v.p),
    t(v.r, OWL.onClass, v.c),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y),
    t(v.y, RDF.type, v.c),
  ], [inconsistent("cls-maxqc1", v.r, v.u, v.p, v.y, v.c)]),
  rule("cls-maxqc2", [
    t(v.r, OWL.maxQualifiedCardinality, ZERO),
    t(v.r, OWL.onProperty, v.p),
    t(v.r, OWL.onClass, OWL.Thing),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y),
  ], [inconsistent("cls-maxqc2", v.r, v.u, v.p, v.y)]),
  rule("cls-maxqc3", [
    t(v.r, OWL.maxQualifiedCardinality, ONE),
    t(v.r, OWL.onProperty, v.p),
    t(v.r, OWL.onClass, v.c),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y1),
    t(v.y1, RDF.type, v.c),
    t(v.u, v.p, v.y2),
    t(v.y2, RDF.type, v.c),
  ], [t(v.y1, OWL.sameAs, v.y2)]),
  rule("cls-maxqc4", [
    t(v.r, OWL.maxQualifiedCardinality, ONE),
    t(v.r, OWL.onProperty, v.p),
    t(v.r, OWL.onClass, OWL.Thing),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y1),
    t(v.u, v.p, v.y2),
  ], [t(v.y1, OWL.sameAs, v.y2)]),
  // A qualified max of one plus an explicitly different value puts that value
  // outside the qualified class.
  rule("cls-maxqc-different", [
    t(v.r, OWL.maxQualifiedCardinality, ONE),
    t(v.r, OWL.onProperty, v.p),
    t(v.r, OWL.onClass, v.c),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y1),
    t(v.y1, RDF.type, v.c),
    t(v.y1, OWL.differentFrom, v.y2),
    t(v.u, v.p, v.y2),
    complementOf,
  ], [...complementHead(v.c), t(v.y2, RDF.type, v.notC)]),
  rule("cls-maxqd1", [
    t(v.r, OWL.maxQualifiedCardinality, ZERO),
    t(v.r, OWL.onProperty, v.p),
    t(v.r, OWL.onDataRange, v.dt),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y),
    t(v.y, RDF.type, v.dt),
  ], [inconsistent("cls-maxqd1", v.r, v.u, v.p, v.y, v.dt)]),
  rule("cls-maxqd2", [
    t(v.r, OWL.maxQualifiedCardinality, ONE),
    t(v.r, OWL.onProperty, v.p),
    t(v.r, OWL.onDataRange, v.dt),
    t(v.u, RDF.type, v.r),
    t(v.u, v.p, v.y1),
    t(v.y1, RDF.type, v.dt),
    t(v.u, v.p, v.y2),
    t(v.y2, RDF.type, v.dt),
  ], [t(v.y1, OWL.sameAs, v.y2)]),
  rule("cls-oo", [t(v.c, OWL.oneOf, v.l), atom("member", v.l, v.i)], [
    t(v.i, RDF.type, v.c),
  ]),
];

const classAxiomRules: Rule[] = [
  rule("cax-sco", [t(v.c1, RDFS.subClassOf, v.c2), t(v.x, RDF.type, v.c1)], [
    t(v.x, RDF.type, v.c2),
  ]),
  rule("cax-eqc1", [
    t(v.c1, OWL.equivalentClass, v.c2),
    t(v.x, RDF.type, v.c1),
  ], [t(v.x, RDF.type, v.c2)]),
  rule("cax-eqc2", [
    t(v.c1, OWL.equivalentClass, v.c2),
    t(v.x, RDF.type, v.c2),
  ], [t(v.x, RDF.type, v.c1)]),
  rule("cax-dw", [
    t(v.c1, OWL.disjointWith, v.c2),
    t(v.x, RDF.type, v.c1),
    t(v.x, RDF.type, v.c2),
  ], [inconsistent("cax-dw", v.c1, v.c2, v.x)]),
  // Each side of a disjointness is a subclass of the other's complement.
  rule("cax-dw-complement2", [
    t(v.c1, OWL.disjointWith, v.c),
    complementOf,
  ], [...complementHead(v.c), t(v.c1, RDFS.subClassOf, v.notC)]),
  rule("cax-dw-complement1", [
    t(v.c, OWL.disjointWith, v.c2),
    complementOf,
  ], [...complementHead(v.c), t(v.c2, RDFS.subClassOf, v.notC)]),
  rule("cax-adc", [
    t(v.adc, RDF.type, OWL.AllDisjointClasses),
    t(v.adc, OWL.members, v.l),
    atom("pair", v.l, v.c1, v.c2),
    t(v.z, RDF.type, v.c1),
    t(v.z, RDF.type, v.c2),
  ], [inconsistent("cax-adc", v.adc, v.c1, v.c2, v.z)]),
  rule("cax-adc-disjoint", [
    t(v.adc, RDF.type, OWL.AllDisjointClasses),
    t(v.adc, OWL.members, v.l),
    atom("pair", v.l, v.c1, v.c2),
  ], [t(v.c1, OWL.disjointWith, v.c2), t(v.c2, OWL.disjointWith, v.c1)]),
];

const datatypeRules: Rule[] = [
  rule("dt-literal", [
    t(v.s, v.p, v.o),
    bind("literal", [v.o], [v.lt], function* (
      [o],
      context,
    ) {
      for (const [member, literal] of literalsOf(o!, context)) {
        if (!isPlainString(literal)) yield [member];
      }
    }),
  ], [atom("literal", v.lt)]),
  rule("dt-string", [t(v.s, v.p, v.o), stringMember(XSD.string)], [
    t(v.lt, RDF.type, XSD.string),
    t(v.lt, RDF.type, RDFS.Literal),
  ]),
  rule("dt-langstring", [t(v.s, v.p, v.o), stringMember(RDF.langString)], [
    t(v.lt, RDF.type, RDF.langString),
    t(v.lt, RDF.type, RDFS.Literal),
  ]),
  rule("dt-type2", [
    atom("literal", v.lt),
    literalMember,
    bind("own-datatype", [v.m], [v.dt], ([m], context) => {
      const literal = context.term(m!) as Literal;
      const datatype = literalDatatype(literal);
      return isInstanceOf(literal, datatype)
        ? [[context.id(dataFactory.namedNode(datatype))]]
        : [];
    }),
  ], [t(v.m, RDF.type, v.dt)]),
  rule("dt-type2-declared", [
    atom("literal", v.lt),
    t(v.dt, RDF.type, RDFS.Datatype),
    literalMember,
    filter("instance-of", [v.m, v.dt], ([m, dt], context) => {
      const datatype = context.term(dt!);
      return datatype.termType === "NamedNode" &&
        isInstanceOf(context.term(m!) as Literal, datatype.value);
    }),
  ], [t(v.m, RDF.type, v.dt)]),
  rule("dt-literal-type", [atom("literal", v.lt), literalMember], [
    t(v.m, RDF.type, RDFS.Literal),
  ]),
  rule("dt-not-type", [
    atom("literal", v.lt),
    t(v.lt, RDF.type, v.dt),
    literalMember,
    filter("invalid-for", [v.m, v.dt], ([m, dt], context) => {
      const datatype = context.term(dt!);
      return datatype.termType === "NamedNode" &&
        isInvalidFor(context.term(m!) as Literal, datatype.value);
    }),
  ], [inconsistent("dt-not-type", v.m, v.dt)]),
];

const schemaRules: Rule[] = [
  rule("scm-cls", [t(v.c, RDF.type, OWL.Class)], [
    t(v.c, RDFS.subClassOf, v.c),
    t(v.c, OWL.equivalentClass, v.c),
    t(v.c, RDFS.subClassOf, OWL.Thing),
    t(OWL.Nothing, RDFS.subClassOf, v.c),
  ]),
  rule("scm-sco", [
    t(v.c1, RDFS.subClassOf, v.c2),
    t(v.c2, RDFS.subClassOf, v.c3),
  ], [t(v.c1, RDFS.subClassOf, v.c3)]),
  rule("scm-eqc1", [t(v.c1, OWL.equivalentClass, v.c2)], [
    t(v.c1, RDFS.subClassOf, v.c2),
    t(v.c2, RDFS.subClassOf, v.c1),
  ]),
  rule("scm-eqc2", [
    t(v.c1, RDFS.subClassOf, v.c2),
    t(v.c2, RDFS.subClassOf, v.c1),
  ], [t(v.c1, OWL.equivalentClass, v.c2)]),
  ...[OWL.ObjectProperty, OWL.DatatypeProperty].map((kind) =>
    rule(kind === OWL.ObjectProperty ? "scm-op" : "scm-dp", [
      t(v.p, RDF.type, kind),
    ], [t(v.p, RDFS.subPropertyOf, v.p), t(v.p, OWL.equivalentProperty, v.p)])
  ),
  rule("scm-spo", [
    t(v.p1, RDFS.subPropertyOf, v.p2),
    t(v.p2, RDFS.subPropertyOf, v.p3),
  ], [t(v.p1, RDFS.subPropertyOf, v.p3)]),
  rule("scm-eqp1", [t(v.p1, OWL.equivalentProperty, v.p2)], [
    t(v.p1, RDFS.subPropertyOf, v.p2),
    t(v.p2, RDFS.subPropertyOf, v.p1),
  ]),
  rule("scm-eqp2", [
    t(v.p1, RDFS.subPropertyOf, v.p2),
    t(v.p2, RDFS.subPropertyOf, v.p1),
  ], [t(v.p1, OWL.equivalentProperty, v.p2)]),
  rule(
    "scm-dom1",
    [t(v.p, RDFS.domain, v.c1), t(v.c1, RDFS.subClassOf, v.c2)],
    [
      t(v.p, RDFS.domain, v.c2),
    ],
  ),
  rule("scm-dom2", [
    t(v.p2, RDFS.domain, v.c),
    t(v.p1, RDFS.subPropertyOf, v.p2),
  ], [t(v.p1, RDFS.domain, v.c)]),
  rule("scm-rng1", [t(v.p, RDFS.range, v.c1), t(v.c1, RDFS.subClassOf, v.c2)], [
    t(v.p, RDFS.range, v.c2),
  ]),
  rule("scm-rng2", [
    t(v.p2, RDFS.range, v.c),
    t(v.p1, RDFS.subPropertyOf, v.p2),
  ], [t(v.p1, RDFS.range, v.c)]),
  // Finite XSD range intersections from the RDF-Based conformance tests.
  rule("scm-rng-short-unsignedInt", [
    t(v.p, RDFS.range, XSD.short),
    t(v.p, RDFS.range, XSD.unsignedInt),
  ], [t(v.p, RDFS.range, XSD.unsignedShort)]),
  rule("scm-rng-sign", [
    t(v.p, RDFS.range, XSD.nonNegativeInteger),
    t(v.p, RDFS.range, XSD.nonPositiveInteger),
  ], [t(v.p, RDFS.range, XSD.short)]),
  rule("scm-hv", [
    t(v.c1, OWL.hasValue, v.i),
    t(v.c1, OWL.onProperty, v.p1),
    t(v.c2, OWL.hasValue, v.i),
    t(v.c2, OWL.onProperty, v.p2),
    t(v.p1, RDFS.subPropertyOf, v.p2),
  ], [t(v.c1, RDFS.subClassOf, v.c2)]),
  rule("scm-svf1", [
    t(v.c1, OWL.someValuesFrom, v.y1),
    t(v.c1, OWL.onProperty, v.p),
    t(v.c2, OWL.someValuesFrom, v.y2),
    t(v.c2, OWL.onProperty, v.p),
    t(v.y1, RDFS.subClassOf, v.y2),
  ], [t(v.c1, RDFS.subClassOf, v.c2)]),
  rule("scm-svf2", [
    t(v.c1, OWL.someValuesFrom, v.y),
    t(v.c1, OWL.onProperty, v.p1),
    t(v.c2, OWL.someValuesFrom, v.y),
    t(v.c2, OWL.onProperty, v.p2),
    t(v.p1, RDFS.subPropertyOf, v.p2),
  ], [t(v.c1, RDFS.subClassOf, v.c2)]),
  rule("scm-avf1", [
    t(v.c1, OWL.allValuesFrom, v.y1),
    t(v.c1, OWL.onProperty, v.p),
    t(v.c2, OWL.allValuesFrom, v.y2),
    t(v.c2, OWL.onProperty, v.p),
    t(v.y1, RDFS.subClassOf, v.y2),
  ], [t(v.c1, RDFS.subClassOf, v.c2)]),
  rule("scm-avf2", [
    t(v.c1, OWL.allValuesFrom, v.y),
    t(v.c1, OWL.onProperty, v.p1),
    t(v.c2, OWL.allValuesFrom, v.y),
    t(v.c2, OWL.onProperty, v.p2),
    t(v.p1, RDFS.subPropertyOf, v.p2),
  ], [t(v.c2, RDFS.subClassOf, v.c1)]),
  rule(
    "scm-int",
    [t(v.c, OWL.intersectionOf, v.l), atom("member", v.l, v.ci)],
    [
      t(v.c, RDFS.subClassOf, v.ci),
    ],
  ),
  rule("scm-uni", [t(v.c, OWL.unionOf, v.l), atom("member", v.l, v.ci)], [
    t(v.ci, RDFS.subClassOf, v.c),
  ]),
];

/** OWL2RL_RULES is the full ruleset, in evaluation order. */
export const OWL2RL_RULES: readonly Rule[] = [
  ...listRules,
  ...equalityRules,
  ...propertyRules,
  ...classRules,
  ...classAxiomRules,
  ...datatypeRules,
  ...schemaRules,
];
