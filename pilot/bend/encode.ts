/**
 * Encodes RDF/JS quads as integer triples for the Bend pilot (reasoner#39).
 *
 * The six vocabulary terms the pilot's rules read are interned first, so their
 * ids are fixed (see {@link V}) and a Bend program can hard-code them. Graph
 * terms are ignored: the pilot reasons over one union graph.
 */
import type { Quad } from "@rdfjs/types";
import { dataFactory } from "@wazoo/sparql-engine/term";
import { TermDictionary } from "@/term-dictionary.ts";

const RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS = "http://www.w3.org/2000/01/rdf-schema#";
const OWL = "http://www.w3.org/2002/07/owl#";

/** VOCABULARY is interned in this order, so each term's id is its index. */
export const VOCABULARY = [
  `${RDF}type`,
  `${RDFS}subClassOf`,
  `${RDFS}domain`,
  `${RDFS}range`,
  `${OWL}inverseOf`,
  `${OWL}TransitiveProperty`,
] as const;

/** V names the fixed ids of {@link VOCABULARY}. */
export const V = {
  type: 0,
  subClassOf: 1,
  domain: 2,
  range: 3,
  inverseOf: 4,
  transitive: 5,
} as const;

/** Encoded is a graph as flat `[s, p, o, s, p, o, ...]` ids plus their terms. */
export interface Encoded {
  readonly triples: Uint32Array;
  readonly dictionary: TermDictionary;
}

/** newDictionary returns a dictionary with {@link VOCABULARY} interned. */
export function newDictionary(): TermDictionary {
  const dictionary = new TermDictionary();
  for (const iri of VOCABULARY) dictionary.id(dataFactory.namedNode(iri));
  return dictionary;
}

/** encode interns every quad's subject, predicate and object. */
export function encode(quads: readonly Quad[]): Encoded {
  const dictionary = newDictionary();
  const triples = new Uint32Array(quads.length * 3);
  quads.forEach((q, i) => {
    triples[i * 3] = dictionary.id(q.subject);
    triples[i * 3 + 1] = dictionary.id(q.predicate);
    triples[i * 3 + 2] = dictionary.id(q.object);
  });
  return { triples, dictionary };
}
