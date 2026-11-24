import type { Quad, Term } from "@rdfjs/types";
import { dataFactory } from "@wazoo/sparql-engine/term";

/**
 * generalizedQuad builds a quad without validating the term positions.
 *
 * OWL 2 RL entails generalized triples (a literal subject, for example, from
 * `eq-sym` or a custom rule), and the `"complete"` closure view lists them.
 * `dataFactory.quad` in `@wazoo/sparql-engine` 0.5 throws on such a position,
 * so the closure builds its quads here and the `"application"` view filters
 * them out.
 */
export function generalizedQuad(
  subject: Term,
  predicate: Term,
  object: Term,
  graph: Term = dataFactory.defaultGraph(),
): Quad {
  return {
    termType: "Quad",
    value: "",
    subject: subject as Quad["subject"],
    predicate: predicate as Quad["predicate"],
    object: object as Quad["object"],
    graph: graph as Quad["graph"],
    equals: (other) =>
      other?.termType === "Quad" && subject.equals(other.subject) &&
      predicate.equals(other.predicate) && object.equals(other.object) &&
      graph.equals(other.graph),
  };
}
