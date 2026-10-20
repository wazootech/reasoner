import type { NamedNode } from "@rdfjs/types";
import { dataFactory } from "@wazoo/sparql-engine/term";

/** RDF_NS is the RDF namespace IRI. */
export const RDF_NS = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
/** RDFS_NS is the RDF Schema namespace IRI. */
export const RDFS_NS = "http://www.w3.org/2000/01/rdf-schema#";
/** OWL_NS is the OWL namespace IRI. */
export const OWL_NS = "http://www.w3.org/2002/07/owl#";
/** XSD_NS is the XML Schema datatypes namespace IRI. */
export const XSD_NS = "http://www.w3.org/2001/XMLSchema#";

function namespace<const Names extends readonly string[]>(
  base: string,
  names: Names,
): { readonly [Name in Names[number]]: NamedNode } {
  const terms: Record<string, NamedNode> = {};
  for (const name of names) terms[name] = dataFactory.namedNode(base + name);
  return terms as { readonly [Name in Names[number]]: NamedNode };
}

/** RDF holds the RDF terms the rules use. */
export const RDF = namespace(
  RDF_NS,
  [
    "type",
    "first",
    "rest",
    "nil",
    "langString",
    "PlainLiteral",
    "XMLLiteral",
  ] as const,
);

/** RDFS holds the RDF Schema terms the rules use. */
export const RDFS = namespace(
  RDFS_NS,
  [
    "subClassOf",
    "subPropertyOf",
    "domain",
    "range",
    "Datatype",
    "Literal",
    "label",
    "comment",
    "seeAlso",
    "isDefinedBy",
  ] as const,
);

/** OWL holds the OWL terms the rules use. */
export const OWL = namespace(
  OWL_NS,
  [
    "sameAs",
    "differentFrom",
    "AllDifferent",
    "members",
    "distinctMembers",
    "Thing",
    "Nothing",
    "Class",
    "NamedIndividual",
    "ObjectProperty",
    "DatatypeProperty",
    "AnnotationProperty",
    "FunctionalProperty",
    "InverseFunctionalProperty",
    "IrreflexiveProperty",
    "SymmetricProperty",
    "AsymmetricProperty",
    "TransitiveProperty",
    "ReflexiveProperty",
    "equivalentClass",
    "equivalentProperty",
    "propertyDisjointWith",
    "AllDisjointProperties",
    "AllDisjointClasses",
    "inverseOf",
    "hasKey",
    "propertyChainAxiom",
    "sourceIndividual",
    "assertionProperty",
    "targetIndividual",
    "targetValue",
    "intersectionOf",
    "unionOf",
    "complementOf",
    "oneOf",
    "someValuesFrom",
    "allValuesFrom",
    "hasValue",
    "onProperty",
    "onClass",
    "onDataRange",
    "maxCardinality",
    "maxQualifiedCardinality",
    "disjointWith",
    "deprecated",
    "versionInfo",
    "priorVersion",
    "backwardCompatibleWith",
    "incompatibleWith",
  ] as const,
);

/** XSD holds the XML Schema datatypes OWL 2 RL supports. */
export const XSD = namespace(
  XSD_NS,
  [
    "decimal",
    "integer",
    "nonNegativeInteger",
    "nonPositiveInteger",
    "positiveInteger",
    "negativeInteger",
    "long",
    "int",
    "short",
    "byte",
    "unsignedLong",
    "unsignedInt",
    "unsignedShort",
    "unsignedByte",
    "float",
    "double",
    "string",
    "normalizedString",
    "token",
    "language",
    "Name",
    "NCName",
    "NMTOKEN",
    "boolean",
    "hexBinary",
    "base64Binary",
    "anyURI",
    "dateTime",
    "dateTimeStamp",
  ] as const,
);
