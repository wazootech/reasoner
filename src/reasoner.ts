import type { NamedNode, Quad, Term } from "@rdfjs/types";
import { dataFactory, termKey } from "@wazoo/sparql-engine/term";
import {
  compileCustomRule,
  type CustomRule,
  type RuleOptions,
} from "@/custom-rule.ts";
import type { Rule } from "@/rule.ts";
import { Engine, type EngineStatistics } from "@/engine.ts";
import type { Fact, Relation } from "@/relation.ts";
import { factKey } from "@/relation.ts";
import {
  AXIOMS,
  complementSkolem,
  INCONSISTENCY,
  isSkolemTerm,
  NONE,
  OWL2RL_RULES,
  RELATIONS,
  TRIPLE,
} from "@/owl2rl/rules.ts";
import {
  OWL,
  OWL_NS,
  RDF,
  RDF_NS,
  RDFS_NS,
  XSD_NS,
} from "@/owl2rl/vocabulary.ts";

const isSkolem = isSkolemTerm;

/**
 * Triple is the part of a quad the reasoner reads. The optional `graph` names
 * the graph the triple is asserted in (the default graph when absent); see
 * {@link GraphMode}.
 */
export type Triple =
  & Pick<Quad, "subject" | "predicate" | "object">
  & { readonly graph?: Term };

/**
 * ClosureView chooses which entailed triples a closure lists.
 *
 * - `"complete"` lists every entailed triple.
 * - `"application"` leaves out the triples a graph store has no use for, as
 *   the Wiki's previous engine did: triples with a literal subject, reflexive
 *   `owl:sameAs`, triples naming a complement-class skolem, and `rdf:type`
 *   triples whose class is a blank node (an anonymous restriction). The
 *   reasoning behind them still happens; only the listing omits them.
 */
export type ClosureView = "complete" | "application";

/** RetractOptions tune {@link Core.retract}. */
export interface RetractOptions {
  /**
   * maxScope is how many asserted triples the connected component of a
   * retraction may hold before `retract` recomputes the whole closure instead
   * of just that component. Defaults to 50,000.
   */
  readonly maxScope?: number;
}

const HUB_NAMESPACES = [RDF_NS, RDFS_NS, OWL_NS, XSD_NS];

/**
 * isHub is `true` for the vocabulary terms every graph shares. They are left
 * out when finding which triples a retraction can affect, because two triples
 * that only share `rdf:type` do not derive anything from each other.
 */
function isHub(term: Term): boolean {
  return term.termType === "NamedNode" &&
    HUB_NAMESPACES.some((namespace) => term.value.startsWith(namespace));
}

/** INSTANCE_VOCABULARY are the vocabulary predicates that relate instances. */
const INSTANCE_VOCABULARY = new Set([
  `${RDF_NS}type`,
  `${OWL_NS}sameAs`,
  `${OWL_NS}differentFrom`,
  "http://www.w3.org/2000/01/rdf-schema#label",
  "http://www.w3.org/2000/01/rdf-schema#comment",
  "http://www.w3.org/2000/01/rdf-schema#seeAlso",
  "http://www.w3.org/2000/01/rdf-schema#isDefinedBy",
]);

/**
 * isInstance is `true` for a triple about individuals: an ordinary property
 * between two terms, `rdf:type` to a class that is not OWL or RDFS vocabulary,
 * `owl:sameAs`, `owl:differentFrom` and annotations. Everything else (the
 * ontology: subclass, domain and range, property characteristics, restrictions,
 * lists) is schema, and retracting it recomputes the whole closure, since a
 * class or property is shared by instances all over the graph.
 */
function isInstance([, p, o]: readonly Term[]): boolean {
  if (p!.termType !== "NamedNode") return false;
  if (!isHub(p!)) return true;
  if (!INSTANCE_VOCABULARY.has(p!.value)) return false;
  return p!.value !== `${RDF_NS}type` || !isHub(o!);
}

/**
 * connectors are the terms of an instance triple that link it to other
 * instance triples: its subject and object. Its predicate and the class of an
 * `rdf:type` triple are schema terms that instances share without depending on
 * each other, so they do not connect.
 */
function connectors(triple: readonly Term[]): Term[] {
  if (!isInstance(triple)) return [];
  const [s, p, o] = triple as [Term, Term, Term];
  const linked = p.value === `${RDF_NS}type` ? [s] : [s, o];
  return linked.filter((term) => !isHub(term));
}

const tripleKey = (s: Term, p: Term, o: Term) =>
  `${termKey(s)} ${termKey(p)} ${termKey(o)}`;

/** shown is `true` when the closure view lists the triple. */
function shown(s: Term, p: Term, o: Term, view: ClosureView): boolean {
  if (p.termType !== "NamedNode") return false;
  if (view === "complete") return true;
  if (s.termType === "Literal") return false;
  if (s.equals(o) && p.equals(OWL.sameAs)) return false;
  if (isSkolem(s) || isSkolem(p) || isSkolem(o)) return false;
  return !(p.equals(RDF.type) && o.termType === "BlankNode");
}

/** Inconsistency is one violated OWL 2 RL `false` rule. */
export interface Inconsistency {
  /** rule is the OWL 2 RL rule name, such as `cax-dw`. */
  readonly rule: string;
  /** terms are the terms the rule matched, in the rule's order. */
  readonly terms: readonly Term[];
  /**
   * graph is the graph whose own closure violates the rule, or
   * {@link DERIVED_GRAPH} when only a combination of graphs does. It is the
   * default graph in `"union"` mode and when only the default graph is used.
   */
  readonly graph: Term;
}

type CoreInconsistency = Omit<Inconsistency, "graph">;

/**
 * Core materializes the OWL 2 RL closure of the triples it is given, as one
 * graph: it ignores the graph term. {@link Reasoner} layers named graphs on top
 * of it.
 *
 * {@link Core.extend} adds more triples to a closure that is already
 * computed and returns only what they entail that was not entailed before,
 * evaluating only the rules the new facts can reach. {@link Core.retract}
 * removes asserted triples and what only they entailed.
 *
 * {@link CustomRule}s, given to the constructor or {@link Reasoner.addRule},
 * run in the same fixpoint as the OWL 2 RL rules. What they derive is stored
 * as triples of the closure, so `closure("complete")` lists it and
 * `closure("application")` lists it under the same filters as any other
 * triple. `extend` stays incremental. `retract` is not: with a custom rule
 * registered it recomputes the whole closure.
 */
class Core {
  #engine!: Engine;
  #triples!: Relation;
  #ran = false;
  /** #asserted holds the triples given to add or extend, not what they entail. */
  #asserted = new Map<string, readonly [Term, Term, Term]>();
  /**
   * #parent and #owned index the asserted triples by connected component: a
   * union-find over the keys of their non-vocabulary terms, and, per root, the
   * keys of the triples in that component. A retraction does not split a
   * component here, so an index can only be coarser than the truth until
   * {@link Core.retract} rebuilds the components it touched.
   */
  #parent = new Map<string, string>();
  #owned = new Map<string, Set<string>>();

  #custom: CustomRule[] = [];
  #compiled: Rule[] = [];

  constructor(options: RuleOptions = {}) {
    for (const rule of options.rules ?? []) this.#register(rule);
    this.#init();
  }

  /**
   * addRule registers a custom rule. The closure is recomputed from the
   * asserted triples the next time it is read or extended, so the rule applies
   * to everything already added. Throws an `Error` for an invalid rule (see
   * {@link CustomRule}); the reasoner is unchanged then.
   */
  addRule(rule: CustomRule): void {
    this.#register(rule);
    this.#init();
    for (const triple of this.#asserted.values()) this.#store(...triple);
    this.#ran = false;
  }

  /** rules lists the custom rules registered so far. */
  get rules(): readonly CustomRule[] {
    return this.#custom;
  }

  #register(rule: CustomRule): void {
    const compiled = compileCustomRule(
      rule,
      new Set(this.#custom.map((r) => r.name)),
    );
    this.#custom.push(rule);
    this.#compiled.push(compiled);
  }

  #init(): void {
    this.#engine = new Engine([...OWL2RL_RULES, ...this.#compiled], {
      equalityRelation: TRIPLE,
      sameAs: OWL.sameAs,
      relations: RELATIONS,
      contentTerm: (term) => term.termType === "Literal",
    });
    this.#triples = this.#engine.relation(TRIPLE);
    for (const [subject, predicate, object] of AXIOMS) {
      this.#store(subject, predicate, object);
    }
  }

  /** statistics count rounds, derivations, and merges across every run. */
  get statistics(): Readonly<EngineStatistics> {
    return this.#engine.statistics;
  }

  /** size is the number of stored facts, before equality classes expand. */
  get size(): number {
    return this.#triples.size;
  }

  /** add queues triples for the next {@link Core.run}. */
  add(triples: Iterable<Triple>): void {
    for (const triple of triples) {
      this.#assert(triple.subject, triple.predicate, triple.object);
    }
  }

  /** run computes the closure of everything added so far. */
  run(): void {
    this.#engine.run();
    this.#ran = true;
  }

  /**
   * extend adds `triples` to the computed closure and returns the triples of
   * the closure that are new: the added triples themselves when they were not
   * already entailed, and everything they entail.
   */
  extend(
    triples: Iterable<Triple>,
    view: ClosureView = "complete",
  ): Quad[] {
    if (!this.#ran) this.run();
    const since = this.#engine.tick();
    this.add(triples);
    this.run();
    const equality = this.#engine.equality;
    const facts = new Set<Fact>();
    for (const fact of this.#triples.facts()) {
      if (fact.bornAt >= since) facts.add(fact);
    }
    // A merge grows the class of a root whose own facts are not renamed, so
    // their expansion gains members too.
    for (const root of equality.rootsChangedSince(since)) {
      for (let column = 0; column < 3; column++) {
        for (const fact of this.#triples.column(column, root)) {
          if (fact.diedAt === Infinity) facts.add(fact);
        }
      }
    }
    const added: Quad[] = [];
    for (const fact of facts) {
      for (const [s, p, o] of this.#expand(fact)) {
        const before = this.#triples.get(factKey([
          equality.findAt(s, since),
          equality.findAt(p, since),
          equality.findAt(o, since),
        ]));
        if (
          before !== undefined && before.bornAt < since &&
          before.diedAt >= since
        ) {
          continue;
        }
        const quad = this.#quad(s, p, o, view);
        if (quad !== undefined) added.push(quad);
      }
    }
    return added;
  }

  /**
   * retract removes asserted `triples` and returns the triples of the closure
   * that are no longer entailed. A triple that was never asserted is ignored,
   * even if it is entailed. The result equals a fresh run on everything
   * asserted but `triples`.
   *
   * Retracting triples about individuals recomputes only their connected
   * component: the triples reachable from them through shared subjects and
   * objects. Classes and properties do not connect, because instances share
   * them without depending on each other. The whole closure is recomputed
   * instead when any retracted triple is schema (subclass, domain, restriction
   * and so on), when the component is larger than
   * {@link RetractOptions.maxScope}, or when it turns out not to be closed
   * (a fact links it to another individual or to a complement class, or an
   * asserted triple outside it names one of its terms).
   *
   * When any {@link CustomRule} is registered, `retract` is not incremental:
   * it always recomputes the whole closure, because a custom rule may relate
   * any triples, so no component is known to be closed. The result is still
   * the same as a fresh run.
   *
   * The result equals a fresh run for every input the differential test in
   * `test/differential/` generates. Rules that derive schema-level facts from
   * instance triples, other than the complement case handled above, are the
   * known place this could be wrong.
   */
  retract(
    triples: Iterable<Triple>,
    view: ClosureView = "complete",
    options: RetractOptions = {},
  ): Quad[] {
    if (!this.#ran) this.run();
    const gone = new Set<string>();
    for (const t of triples) {
      const key = tripleKey(t.subject, t.predicate, t.object);
      if (this.#asserted.has(key)) gone.add(key);
    }
    if (gone.size === 0) return [];
    // A custom rule can derive anything from anything, so the component
    // analysis below (which assumes the OWL 2 RL rules) does not hold.
    const scope = this.#custom.length > 0 ? undefined : this.#component(gone);
    const goneTriples = new Map(
      [...gone].map((key) => [key, this.#asserted.get(key)!] as const),
    );
    for (const key of gone) this.#asserted.delete(key);
    if (scope !== undefined) this.#reindex(scope, goneTriples);
    if (scope !== undefined && scope.size <= (options.maxScope ?? 50_000)) {
      const removed = this.#recompute(
        scope,
        gone,
        [...goneTriples.values()],
        view,
      );
      if (removed !== undefined) return removed;
    }
    return this.#rebuild(view);
  }

  /** nodes are the keys of the terms of a triple that connect components. */
  #nodes(triple: readonly Term[]): string[] {
    return connectors(triple).map(termKey);
  }

  #find(key: string): string {
    let root = key;
    while (this.#parent.get(root) !== root) root = this.#parent.get(root)!;
    while (this.#parent.get(key) !== root) {
      const next = this.#parent.get(key)!;
      this.#parent.set(key, root);
      key = next;
    }
    return root;
  }

  /** link files the asserted triple under the component of its terms. */
  #link(key: string, triple: readonly Term[]): void {
    const nodes = this.#nodes(triple);
    if (nodes.length === 0) return;
    for (const node of nodes) {
      if (!this.#parent.has(node)) {
        this.#parent.set(node, node);
        this.#owned.set(node, new Set());
      }
    }
    let root = this.#find(nodes[0]!);
    for (let i = 1; i < nodes.length; i++) {
      let other = this.#find(nodes[i]!);
      if (other === root) continue;
      if (this.#owned.get(other)!.size > this.#owned.get(root)!.size) {
        [root, other] = [other, root];
      }
      const into = this.#owned.get(root)!;
      for (const owned of this.#owned.get(other)!) into.add(owned);
      this.#owned.delete(other);
      this.#parent.set(other, root);
    }
    this.#owned.get(root)!.add(key);
  }

  /**
   * component returns the keys of the asserted triples connected to `gone`,
   * or `undefined` when `gone` touches only vocabulary terms.
   */
  #component(gone: ReadonlySet<string>): Set<string> | undefined {
    const roots = new Set<string>();
    for (const key of gone) {
      if (!isInstance(this.#asserted.get(key)!)) return undefined;
    }
    for (const key of gone) {
      const [first] = this.#nodes(this.#asserted.get(key)!);
      if (first !== undefined) roots.add(this.#find(first));
    }
    if (roots.size === 0) return undefined;
    const scope = new Set<string>();
    for (const root of roots) {
      for (const key of this.#owned.get(root)!) scope.add(key);
    }
    return scope;
  }

  /**
   * reindex splits the components of `scope` again, now that the retracted
   * triples are gone, so they do not stay merged for good.
   */
  #reindex(
    scope: ReadonlySet<string>,
    gone: ReadonlyMap<string, readonly [Term, Term, Term]>,
  ): void {
    const triple = (key: string) => this.#asserted.get(key) ?? gone.get(key)!;
    const nodes = new Set<string>();
    for (const key of scope) {
      for (const node of this.#nodes(triple(key))) nodes.add(node);
    }
    for (const node of nodes) this.#owned.delete(this.#find(node));
    for (const node of nodes) this.#parent.delete(node);
    for (const key of scope) {
      const kept = this.#asserted.get(key);
      if (kept !== undefined) this.#link(key, kept);
    }
  }

  /**
   * recompute drops every fact that mentions a term of the component, splits
   * its `owl:sameAs` classes, asserts the component's remaining triples again
   * and runs to a fixpoint. It returns `undefined`, having changed nothing,
   * when the component is not closed (a fact or class links it to a term
   * outside it), so the caller can recompute everything.
   */
  #recompute(
    scope: ReadonlySet<string>,
    gone: ReadonlySet<string>,
    goneTriples: readonly (readonly [Term, Term, Term])[],
    view: ClosureView,
  ): Quad[] | undefined {
    const engine = this.#engine;
    const terms = engine.terms;
    const equality = engine.equality;
    const queue: Term[] = goneTriples.flatMap(connectors);
    for (const key of scope) {
      if (!gone.has(key)) queue.push(...connectors(this.#asserted.get(key)!));
    }
    const ids = new Set<number>();
    while (queue.length > 0) {
      const term = queue.pop()!;
      const id = terms.lookup(term);
      if (id !== undefined) ids.add(id);
      // The complement class of a term is a skolem the rules mint on demand.
      const skolem = terms.lookup(complementSkolem(term));
      if (skolem !== undefined && !ids.has(skolem)) {
        queue.push(terms.term(skolem));
      }
    }
    for (const id of [...ids]) {
      for (const member of equality.members(equality.find(id))) ids.add(member);
    }
    for (const id of ids) if (isHub(terms.term(id))) return undefined;
    const facts = engine.mentioning(ids);
    for (const [relation, group] of facts) {
      for (const fact of group) {
        for (let column = 0; column < fact.args.length; column++) {
          if (relation.name === INCONSISTENCY && column === 0) continue;
          const arg = fact.args[column]!;
          if (ids.has(arg)) continue;
          // Schema terms (classes, properties, vocabulary) are shared; another
          // instance in a fact means the component is not closed.
          const outside = terms.term(arg);
          if (this.#parent.has(termKey(outside))) return undefined;
          // A complement skolem was minted from these instances, and its own
          // facts (which name no instance) would outlive the purge.
          if (isSkolem(outside)) return undefined;
        }
      }
    }
    const before = new Map<string, Quad>();
    for (const fact of facts.get(this.#triples) ?? []) {
      for (const [s, p, o] of this.#expand(fact)) {
        // An asserted triple outside the component that names one of its
        // terms (a class used as an individual, say) would be purged and not
        // asserted again, so the whole closure is recomputed instead.
        const key = tripleKey(terms.term(s), terms.term(p), terms.term(o));
        if (this.#asserted.has(key) && !scope.has(key)) return undefined;
        const quad = this.#quad(s, p, o, "complete");
        if (quad !== undefined) {
          before.set(
            tripleKey(quad.subject, quad.predicate, quad.object),
            quad,
          );
        }
      }
    }
    engine.purge(ids, facts);
    engine.record();
    for (const key of scope) {
      const triple = this.#asserted.get(key);
      if (triple !== undefined) this.#store(...triple);
    }
    engine.run();
    for (const fact of engine.stopRecording()) {
      if (fact.diedAt !== Infinity) continue;
      if (this.#triples.get(fact.key) !== fact) continue;
      for (const [s, p, o] of this.#expand(fact)) {
        before.delete(tripleKey(terms.term(s), terms.term(p), terms.term(o)));
      }
    }
    return [...before.values()].filter((quad) =>
      shown(quad.subject, quad.predicate, quad.object, view)
    );
  }

  /** rebuild recomputes the whole closure from the asserted triples. */
  #rebuild(view: ClosureView): Quad[] {
    const old = new Map<string, Quad>();
    for (const quad of this.closure("complete")) {
      old.set(tripleKey(quad.subject, quad.predicate, quad.object), quad);
    }
    this.#init();
    for (const triple of this.#asserted.values()) this.#store(...triple);
    this.run();
    for (const quad of this.closure("complete")) {
      old.delete(tripleKey(quad.subject, quad.predicate, quad.object));
    }
    return [...old.values()].filter((quad) =>
      shown(quad.subject, quad.predicate, quad.object, view)
    );
  }

  /**
   * closure yields every triple of the closure, the axiomatic triples
   * included, with each `owl:sameAs` class expanded to its members.
   */
  *closure(view: ClosureView = "complete"): Generator<Quad> {
    if (!this.#ran) this.run();
    for (const fact of this.#triples.facts()) {
      for (const [s, p, o] of this.#expand(fact)) {
        const quad = this.#quad(s, p, o, view);
        if (quad !== undefined) yield quad;
      }
    }
  }

  /** has is `true` when the closure entails the triple. */
  has(subject: Term, predicate: Term, object: Term): boolean {
    if (!this.#ran) this.run();
    const terms = this.#engine.terms;
    const ids = [subject, predicate, object].map((term) => terms.lookup(term));
    if (ids.some((id) => id === undefined)) return false;
    const equality = this.#engine.equality;
    return this.#triples.has(ids.map((id) => equality.find(id!)));
  }

  /** inconsistencies lists every OWL 2 RL `false` rule the closure violates. */
  inconsistencies(): CoreInconsistency[] {
    if (!this.#ran) this.run();
    const terms = this.#engine.terms;
    const none = terms.id(NONE);
    const reports: CoreInconsistency[] = [];
    for (const fact of this.#engine.relation(INCONSISTENCY).facts()) {
      const [rule, ...matched] = fact.args;
      reports.push({
        rule: terms.term(rule!).value,
        terms: matched.filter((id) => id !== none).map((id) => terms.term(id)),
      });
    }
    return reports;
  }

  #assert(subject: Term, predicate: Term, object: Term): void {
    const key = tripleKey(subject, predicate, object);
    if (!this.#asserted.has(key)) {
      const triple = [subject, predicate, object] as const;
      this.#asserted.set(key, triple);
      this.#link(key, triple);
    }
    this.#store(subject, predicate, object);
  }

  #store(subject: Term, predicate: Term, object: Term): void {
    const terms = this.#engine.terms;
    this.#engine.add(TRIPLE, [
      terms.id(subject),
      terms.id(predicate),
      terms.id(object),
    ]);
  }

  *#expand(fact: Fact): Generator<[number, number, number]> {
    const equality = this.#engine.equality;
    const [s, p, o] = fact.args as [number, number, number];
    for (const subject of equality.members(s)) {
      for (const predicate of equality.members(p)) {
        for (const object of equality.members(o)) {
          yield [subject, predicate, object];
        }
      }
    }
  }

  #quad(
    s: number,
    p: number,
    o: number,
    view: ClosureView,
  ): Quad | undefined {
    const terms = this.#engine.terms;
    const predicate = terms.term(p);
    const subject = terms.term(s);
    const object = terms.term(o);
    if (!shown(subject, predicate, object, view)) return undefined;
    return dataFactory.quad(
      subject as Quad["subject"],
      predicate as NamedNode,
      object as Quad["object"],
    );
  }
}

/**
 * DERIVED_GRAPH is the graph a triple lands in when it is entailed only by a
 * combination of graphs: no single graph entails it on its own.
 */
export const DERIVED_GRAPH: NamedNode = dataFactory.namedNode(
  "https://wazoo.dev/ns/reasoner#derived",
);

/**
 * GraphMode chooses how a {@link Reasoner} treats the graph term of a quad.
 *
 * - `"per-graph"` (the default) keeps graphs apart. The closure lists each
 *   entailed triple in the graphs whose own closure entails it. A triple that
 *   is entailed only by premises from several graphs goes in
 *   {@link DERIVED_GRAPH}. Triples entailed by no premise at all (the axiomatic
 *   triples) are in the default graph. Entailment itself still sees every
 *   graph, so cross-graph consequences are found and nothing is lost; the
 *   graphs only decide where each triple is listed.
 * - `"union"` merges every graph into one closure, as if the graph term were
 *   ignored, and lists it all in the default graph.
 *
 * Callers that use only the default graph get the same closure in both modes.
 */
export type GraphMode = "per-graph" | "union";

/** ReasonerOptions configure a {@link Reasoner}. */
export interface ReasonerOptions {
  /** graphs is the {@link GraphMode}. Defaults to `"per-graph"`. */
  readonly graphs?: GraphMode;
  /** rules are custom rules to evaluate alongside the OWL 2 RL rules. */
  readonly rules?: readonly CustomRule[];
}

const DEFAULT_KEY = termKey(dataFactory.defaultGraph());
const DERIVED_KEY = termKey(DERIVED_GRAPH);

const graphKey = (graph: Term | undefined): string =>
  graph === undefined ? DEFAULT_KEY : termKey(graph);

let baseKeys: Set<string> | undefined;
/** base is the triples entailed by nothing: the axiomatic triples. */
function base(): Set<string> {
  if (baseKeys === undefined) {
    baseKeys = new Set();
    for (const q of new Core().closure("complete")) {
      baseKeys.add(tripleKey(q.subject, q.predicate, q.object));
    }
  }
  return baseKeys;
}

/** PerGraph is the closure of one graph taken alone. */
interface PerGraph {
  readonly core: Core;
  readonly keys: Set<string>;
}

/**
 * Reasoner materializes the OWL 2 RL closure of the quads it is given, with
 * named graphs (see {@link GraphMode}).
 *
 * ```ts
 * const reasoner = new Reasoner();
 * reasoner.add(quads);
 * reasoner.run();
 * for (const quad of reasoner.closure()) store.add(quad);
 * ```
 *
 * {@link Reasoner.extend} adds more quads to a closure that is already
 * computed and returns only what they entail that was not entailed before,
 * evaluating only the rules the new facts can reach. {@link Reasoner.retract}
 * removes asserted quads and what only they entailed. A triple asserted in two
 * graphs stays asserted until it is retracted from both.
 *
 * Internally one incremental closure holds the union of all graphs. With more
 * than one graph in `"per-graph"` mode, the closure of each graph alone is also
 * computed, lazily, to decide which graphs list a triple; `extend` and
 * `retract` then diff the listings, which costs a pass over the closure.
 */
export class Reasoner {
  readonly #mode: GraphMode;
  readonly #union: Core;
  /** #graphs are the graphs with asserted triples, and those triples. */
  readonly #graphs = new Map<
    string,
    { graph: Term; triples: Map<string, Triple> }
  >();
  /** #refs counts the graphs each asserted triple is asserted in. */
  readonly #refs = new Map<string, number>();
  #per: Map<string, PerGraph> | undefined;

  constructor(options: ReasonerOptions = {}) {
    this.#mode = options.graphs ?? "per-graph";
    this.#union = new Core({ rules: options.rules });
  }

  /**
   * addRule registers a custom rule. The closure is recomputed from the
   * asserted quads on the next read. See {@link CustomRule}.
   */
  addRule(rule: CustomRule): void {
    this.#union.addRule(rule);
    this.#per = undefined;
  }

  /** rules lists the custom rules registered so far. */
  get rules(): readonly CustomRule[] {
    return this.#union.rules;
  }

  /** statistics count rounds, derivations, and merges across every run. */
  get statistics(): Readonly<EngineStatistics> {
    return this.#union.statistics;
  }

  /** size is the number of stored facts, before equality classes expand. */
  get size(): number {
    return this.#union.size;
  }

  /** add queues quads for the next {@link Reasoner.run}. */
  add(quads: Iterable<Triple>): void {
    const all = [...quads];
    for (const quad of all) this.#register(quad);
    this.#union.add(all);
  }

  /** run computes the closure of everything added so far. */
  run(): void {
    this.#union.run();
  }

  /**
   * extend adds `quads` to the computed closure and returns the quads of the
   * closure that are new: the added ones when they were not already entailed in
   * their graph, and everything they entail.
   */
  extend(quads: Iterable<Triple>, view: ClosureView = "complete"): Quad[] {
    const all = [...quads];
    const after = new Set(this.#graphs.keys());
    for (const quad of all) after.add(graphKey(quad.graph));
    const diffing = this.#mode === "per-graph" && after.size > 1;
    const before = diffing ? this.#listing() : undefined;
    for (const quad of all) this.#register(quad);
    const added = this.#union.extend(all, diffing ? "complete" : view);
    if (before === undefined) return this.#label(added);
    return this.#difference(this.#listing(), before, view);
  }

  /**
   * retract removes asserted `quads` and returns the quads of the closure that
   * are no longer entailed. A quad that was not asserted in its graph is
   * ignored, even if it is entailed. The result equals a fresh run on
   * everything asserted but `quads`.
   */
  retract(
    quads: Iterable<Triple>,
    view: ClosureView = "complete",
    options: RetractOptions = {},
  ): Quad[] {
    const gone = new Map<string, Triple>();
    const counts = new Map<string, number>();
    for (const quad of quads) {
      const key = tripleKey(quad.subject, quad.predicate, quad.object);
      const id = `${graphKey(quad.graph)}\0${key}`;
      if (gone.has(id)) continue;
      if (this.#graphs.get(graphKey(quad.graph))?.triples.has(key)) {
        gone.set(id, quad);
        counts.set(key, (counts.get(key) ?? 0) + 1);
      }
    }
    if (gone.size === 0) return [];
    const diffing = this.#mode === "per-graph" && this.#graphs.size > 1;
    const before = diffing ? this.#listing() : undefined;
    // A triple asserted in another graph too stays asserted.
    const lost: Triple[] = [];
    for (const quad of gone.values()) {
      const key = tripleKey(quad.subject, quad.predicate, quad.object);
      if (this.#refs.get(key) === counts.get(key)) lost.push(quad);
    }
    const removed = this.#union.retract(
      lost,
      diffing ? "complete" : view,
      options,
    );
    // Labels come from the graphs as they were, so label before unregistering.
    const labelled = before === undefined ? this.#label(removed) : [];
    for (const quad of gone.values()) this.#unregister(quad);
    if (before === undefined) return labelled;
    return this.#difference(before, this.#listing(), view);
  }

  /**
   * closure yields every quad of the closure, the axiomatic triples included,
   * with each `owl:sameAs` class expanded to its members. See
   * {@link GraphMode} for which graph lists each triple.
   */
  *closure(view: ClosureView = "complete"): Generator<Quad> {
    if (this.#plain) {
      yield* this.#union.closure(view);
      return;
    }
    for (const quad of this.#union.closure(view)) {
      yield* this.#label([quad]);
    }
  }

  /**
   * has is `true` when the closure entails the triple. With a `graph`, it is
   * `true` only when that graph lists the triple. In `"union"` mode the closure
   * is all in the default graph, so any other `graph` gives `false`.
   */
  has(subject: Term, predicate: Term, object: Term, graph?: Term): boolean {
    if (!this.#union.has(subject, predicate, object)) return false;
    if (graph === undefined) return true;
    const key = graphKey(graph);
    if (this.#plain) return key === DEFAULT_KEY;
    return this.#labelsOf(tripleKey(subject, predicate, object)).includes(key);
  }

  /**
   * inconsistencies lists every OWL 2 RL `false` rule the closure violates.
   * Each names the graph whose own closure violates the rule, or
   * {@link DERIVED_GRAPH} for a rule violated only by combining graphs.
   */
  inconsistencies(): Inconsistency[] {
    const all = this.#union.inconsistencies();
    if (this.#plain) {
      const graph = dataFactory.defaultGraph();
      return all.map((report) => ({ ...report, graph }));
    }
    if (!this.#multi) {
      const [{ graph }] = this.#graphs.values();
      return all.map((report) => ({ ...report, graph }));
    }
    const reports: Inconsistency[] = [];
    const known = new Set<string>();
    for (const [key, { core }] of this.#perGraphs()) {
      for (const report of core.inconsistencies()) {
        known.add(report.rule);
        reports.push({ ...report, graph: this.#graphTerm(key) });
      }
    }
    for (const report of all) {
      if (!known.has(report.rule)) {
        reports.push({ ...report, graph: DERIVED_GRAPH });
      }
    }
    return reports;
  }

  /** #plain is `true` when every triple is listed in the default graph. */
  get #plain(): boolean {
    if (this.#mode === "union" || this.#graphs.size === 0) return true;
    return this.#graphs.size === 1 && this.#graphs.has(DEFAULT_KEY);
  }

  /** #multi is `true` when per-graph closures are needed to label triples. */
  get #multi(): boolean {
    return this.#mode === "per-graph" && this.#graphs.size > 1;
  }

  #register(quad: Triple): void {
    const key = tripleKey(quad.subject, quad.predicate, quad.object);
    const gk = graphKey(quad.graph);
    let entry = this.#graphs.get(gk);
    if (entry === undefined) {
      entry = {
        graph: quad.graph ?? dataFactory.defaultGraph(),
        triples: new Map(),
      };
      this.#graphs.set(gk, entry);
    }
    if (entry.triples.has(key)) return;
    entry.triples.set(key, quad);
    this.#refs.set(key, (this.#refs.get(key) ?? 0) + 1);
    this.#per = undefined;
  }

  #unregister(quad: Triple): void {
    const key = tripleKey(quad.subject, quad.predicate, quad.object);
    const gk = graphKey(quad.graph);
    const entry = this.#graphs.get(gk)!;
    entry.triples.delete(key);
    if (entry.triples.size === 0) this.#graphs.delete(gk);
    const refs = this.#refs.get(key)! - 1;
    if (refs === 0) this.#refs.delete(key);
    else this.#refs.set(key, refs);
    this.#per = undefined;
  }

  /** #perGraphs computes the closure of each graph alone, once per change. */
  #perGraphs(): Map<string, PerGraph> {
    if (this.#per !== undefined) return this.#per;
    const per = new Map<string, PerGraph>();
    for (const [key, { triples }] of this.#graphs) {
      const core = new Core({ rules: this.#union.rules });
      core.add(triples.values());
      core.run();
      const keys = new Set<string>();
      for (const q of core.closure("complete")) {
        keys.add(tripleKey(q.subject, q.predicate, q.object));
      }
      per.set(key, { core, keys });
    }
    return this.#per = per;
  }

  #graphTerm(key: string): Term {
    if (key === DEFAULT_KEY) return dataFactory.defaultGraph();
    if (key === DERIVED_KEY) return DERIVED_GRAPH;
    return this.#graphs.get(key)!.graph;
  }

  /**
   * #labelsOf returns the keys of the graphs that list an entailed triple: the
   * default graph for an axiom, each graph that asserts it or entails it alone,
   * else the derived graph.
   */
  #labelsOf(key: string): string[] {
    const labels = new Set<string>();
    const axiom = base().has(key);
    if (axiom) labels.add(DEFAULT_KEY);
    const per = this.#multi ? this.#perGraphs() : undefined;
    for (const [gk, { triples }] of this.#graphs) {
      const alone = per === undefined || per.get(gk)!.keys.has(key);
      if (triples.has(key) || (alone && !axiom)) labels.add(gk);
    }
    if (labels.size === 0) labels.add(DERIVED_KEY);
    return [...labels];
  }

  /** #label places each default-graph quad of the closure in its graphs. */
  #label(quads: readonly Quad[]): Quad[] {
    if (this.#plain) return [...quads];
    const out: Quad[] = [];
    for (const { subject, predicate, object } of quads) {
      const key = tripleKey(subject, predicate, object);
      for (const gk of this.#labelsOf(key)) {
        out.push(dataFactory.quad(
          subject,
          predicate,
          object,
          this.#graphTerm(gk) as Quad["graph"],
        ));
      }
    }
    return out;
  }

  /** #listing is the complete closure keyed by graph and triple. */
  #listing(): Map<string, Quad> {
    const listing = new Map<string, Quad>();
    for (const quad of this.closure("complete")) {
      const key = tripleKey(quad.subject, quad.predicate, quad.object);
      listing.set(`${graphKey(quad.graph)}\0${key}`, quad);
    }
    return listing;
  }

  /** #difference lists the quads of `from` that `without` lacks, in `view`. */
  #difference(
    from: Map<string, Quad>,
    without: Map<string, Quad>,
    view: ClosureView,
  ): Quad[] {
    const out: Quad[] = [];
    for (const [key, quad] of from) {
      if (
        !without.has(key) &&
        shown(quad.subject, quad.predicate, quad.object, view)
      ) out.push(quad);
    }
    return out;
  }
}
