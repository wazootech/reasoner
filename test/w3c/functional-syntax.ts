/**
 * A converter from the subset of OWL 2 functional syntax that the W3C RL
 * tests without an RDF/XML form use, to RDF triples (OWL 2 Mapping to RDF
 * Graphs). It throws on anything outside the subset, so a new test cannot
 * pass or fail for a construct the converter silently dropped.
 */
import type { BlankNode, NamedNode, Quad, Term } from "@rdfjs/types";
import { dataFactory as df } from "@wazoo/sparql-engine/term";

const RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS = "http://www.w3.org/2000/01/rdf-schema#";
const OWL = "http://www.w3.org/2002/07/owl#";

type Node = string | { name: string; args: Node[] };

/** tokenize splits functional syntax into parens, quoted literals and words. */
function tokenize(text: string): string[] {
  const tokens = text.match(
    /"(?:[^"\\]|\\.)*"(?:\^\^[^\s()]+|@[A-Za-z-]+)?|[()]|<[^>]*>|[^\s()]+/g,
  );
  return tokens ?? [];
}

function parse(tokens: string[]): Node[] {
  let at = 0;
  const read = (): Node => {
    const token = tokens[at++]!;
    if (tokens[at] !== "(") return token;
    at++;
    const args: Node[] = [];
    while (tokens[at] !== ")") {
      if (at >= tokens.length) throw new Error("unbalanced parentheses");
      args.push(read());
    }
    at++;
    return { name: token, args };
  };
  const out: Node[] = [];
  while (at < tokens.length) out.push(read());
  return out;
}

/** functionalSyntaxToQuads converts an `Ontology(...)` document to triples. */
export function functionalSyntaxToQuads(text: string): Quad[] {
  const prefixes = new Map<string, string>();
  const body = text.replace(
    /Prefix\(\s*([\w-]*):\s*=\s*<([^>]*)>\s*\)/g,
    (_, name: string, iri: string) => {
      prefixes.set(name, iri);
      return "";
    },
  );
  const quads: Quad[] = [];
  let blanks = 0;
  const bnode = (): BlankNode => df.blankNode(`fs${blanks++}`);
  const iri = (token: string): NamedNode => {
    if (token.startsWith("<")) return df.namedNode(token.slice(1, -1));
    const colon = token.indexOf(":");
    const base = prefixes.get(token.slice(0, colon));
    if (colon < 0 || base === undefined) {
      throw new Error(`unknown prefix in ${token}`);
    }
    return df.namedNode(base + token.slice(colon + 1));
  };
  const literal = (token: string): Term => {
    const m = /^"((?:[^"\\]|\\.)*)"(?:\^\^(\S+)|@([A-Za-z-]+))?$/.exec(token)!;
    if (m[3] !== undefined) return df.literal(m[1]!, m[3]);
    if (m[2] !== undefined) return df.literal(m[1]!, iri(m[2]));
    return df.literal(m[1]!);
  };
  const add = (s: Term, p: string, o: Term) =>
    quads.push(
      df.quad(
        s as Quad["subject"],
        df.namedNode(p),
        o as Quad["object"],
      ),
    );
  const atom = (node: Node): string => {
    if (typeof node !== "string") {
      throw new Error(`unsupported functional syntax: ${node.name}`);
    }
    return node;
  };
  const term = (node: Node): Term =>
    atom(node).startsWith('"') ? literal(atom(node)) : iri(atom(node));

  const classExpression = (node: Node): Term => {
    if (typeof node === "string") return iri(node);
    const [a, b] = node.args;
    if (node.name === "ObjectComplementOf") {
      const c = bnode();
      add(c, `${RDF}type`, df.namedNode(`${OWL}Class`));
      add(c, `${OWL}complementOf`, classExpression(a!));
      return c;
    }
    if (node.name === "DataHasValue") {
      const r = bnode();
      add(r, `${RDF}type`, df.namedNode(`${OWL}Restriction`));
      add(r, `${OWL}onProperty`, term(a!));
      add(r, `${OWL}hasValue`, term(b!));
      return r;
    }
    throw new Error(`unsupported functional syntax: ${node.name}`);
  };
  const list = (members: Term[]): Term => {
    let tail: Term = df.namedNode(`${RDF}nil`);
    for (const member of [...members].reverse()) {
      const cell = bnode();
      add(cell, `${RDF}first`, member);
      add(cell, `${RDF}rest`, tail);
      tail = cell;
    }
    return tail;
  };

  const DECLARED: Record<string, string> = {
    Class: "Class",
    ObjectProperty: "ObjectProperty",
    DataProperty: "DatatypeProperty",
    NamedIndividual: "NamedIndividual",
  };
  const PROPERTY_KINDS: Record<string, string> = {
    FunctionalDataProperty: "FunctionalProperty",
    FunctionalObjectProperty: "FunctionalProperty",
    TransitiveObjectProperty: "TransitiveProperty",
  };
  const ontology = parse(tokenize(body)).find((n) =>
    typeof n !== "string" && n.name === "Ontology"
  );
  if (ontology === undefined || typeof ontology === "string") {
    throw new Error("no Ontology(...) in functional syntax");
  }
  for (const axiom of ontology.args) {
    if (typeof axiom === "string") throw new Error(`stray token ${axiom}`);
    const [a, b, c] = axiom.args;
    if (axiom.name === "Declaration") {
      const decl = a as { name: string; args: Node[] };
      const kind = DECLARED[decl.name];
      if (kind === undefined) {
        throw new Error(`unsupported functional syntax: ${decl.name}`);
      }
      add(term(decl.args[0]!), `${RDF}type`, df.namedNode(OWL + kind));
    } else if (axiom.name in PROPERTY_KINDS) {
      add(
        term(a!),
        `${RDF}type`,
        df.namedNode(OWL + PROPERTY_KINDS[axiom.name]),
      );
    } else if (axiom.name === "ClassAssertion") {
      add(term(b!), `${RDF}type`, classExpression(a!));
    } else if (axiom.name === "DataPropertyAssertion") {
      add(term(b!), iri(atom(a!)).value, term(c!));
    } else if (axiom.name === "DataPropertyRange") {
      add(term(a!), `${RDFS}range`, term(b!));
    } else if (axiom.name === "SubObjectPropertyOf") {
      if (typeof a !== "string" && a!.name === "ObjectPropertyChain") {
        add(term(b!), `${OWL}propertyChainAxiom`, list(a!.args.map(term)));
      } else add(term(a!), `${RDFS}subPropertyOf`, term(b!));
    } else {
      throw new Error(`unsupported functional syntax: ${axiom.name}`);
    }
  }
  return quads;
}
