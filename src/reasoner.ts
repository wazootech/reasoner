import type { NamedNode, Quad, Term } from "@rdfjs/types";
import { dataFactory, termKey } from "@wazoo/sparql-engine/term";
import { Engine, type EngineStatistics } from "@/engine.ts";
import type { Fact, Relation } from "@/relation.ts";
import { factKey } from "@/relation.ts";
import {
  AXIOMS,
  COMPLEMENT_PREFIX,
  complementSkolem,
  INCONSISTENCY,
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

function isSkolem(term: Term): boolean {
  return term.termType === "NamedNode" &&
    term.value.startsWith(COMPLEMENT_PREFIX);
}

/** Triple is the part of a quad the reasoner reads; the graph is ignored. */
export type Triple = Pick<Quad, "subject" | "predicate" | "object">;

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

/** RetractOptions tune {@link Reasoner.retract}. */
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
}

/**
 * Reasoner materializes the OWL 2 RL closure of the triples it is given.
 *
 * ```ts
 * const reasoner = new Reasoner();
 * reasoner.add(quads);
 * reasoner.run();
 * for (const quad of reasoner.closure()) graph.add(quad);
 * ```
 *
 * {@link Reasoner.extend} adds more triples to a closure that is already
 * computed and returns only what they entail that was not entailed before,
 * evaluating only the rules the new facts can reach. {@link Reasoner.retract}
 * removes asserted triples and what only they entailed.
 */
export class Reasoner {
  #engine!: Engine;
  #triples!: Relation;
  #ran = false;
  /** #asserted holds the triples given to add or extend, not what they entail. */
  #asserted = new Map<string, readonly [Term, Term, Term]>();

  constructor() {
    this.#init();
  }

  #init(): void {
    this.#engine = new Engine(OWL2RL_RULES, {
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

  /** add queues triples for the next {@link Reasoner.run}. */
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
   * Only the connected component of the retracted triples is recomputed: the
   * triples reachable from them through shared terms (vocabulary terms such as
   * `rdf:type` do not connect). A component larger than
   * {@link RetractOptions.maxScope}, one that reaches vocabulary terms
   * through `owl:sameAs`, and a retraction touching only vocabulary terms
   * recompute the whole closure instead.
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
    const scope = this.#component(gone);
    const goneTriples = [...gone].map((key) => this.#asserted.get(key)!);
    for (const key of gone) this.#asserted.delete(key);
    if (scope !== undefined && scope.size <= (options.maxScope ?? 50_000)) {
      const removed = this.#recompute(scope, gone, goneTriples, view);
      if (removed !== undefined) return removed;
    }
    return this.#rebuild(view);
  }

  /**
   * component returns the keys of the asserted triples connected to `gone`,
   * or `undefined` when `gone` touches only vocabulary terms.
   */
  #component(gone: ReadonlySet<string>): Set<string> | undefined {
    const parent = new Map<string, string>();
    const find = (x: string): string => {
      let root = x;
      while (parent.get(root) !== root) root = parent.get(root)!;
      while (parent.get(x) !== root) {
        const next = parent.get(x)!;
        parent.set(x, root);
        x = next;
      }
      return root;
    };
    const nodes = (triple: readonly Term[]) =>
      triple.filter((term) => !isHub(term)).map(termKey);
    for (const triple of this.#asserted.values()) {
      const keys = nodes(triple);
      for (const key of keys) if (!parent.has(key)) parent.set(key, key);
      for (let i = 1; i < keys.length; i++) {
        parent.set(find(keys[i]!), find(keys[0]!));
      }
    }
    const roots = new Set<string>();
    for (const key of gone) {
      const [first] = nodes(this.#asserted.get(key)!);
      if (first !== undefined) roots.add(find(first));
    }
    if (roots.size === 0) return undefined;
    const scope = new Set<string>();
    for (const [key, triple] of this.#asserted) {
      const [first] = nodes(triple);
      if (first !== undefined && roots.has(find(first))) scope.add(key);
    }
    return scope;
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
    const members: Term[] = goneTriples.flat();
    for (const key of scope) {
      if (!gone.has(key)) members.push(...this.#asserted.get(key)!);
    }
    const ids = new Set<number>();
    const queue = members.filter((term) => !isHub(term));
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
          const term = terms.term(arg);
          if (!isHub(term) && !term.equals(NONE)) return undefined;
        }
      }
    }
    const before = new Map<string, Quad>();
    for (const fact of facts.get(this.#triples) ?? []) {
      for (const [s, p, o] of this.#expand(fact)) {
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
    const since = engine.tick();
    for (const key of scope) {
      const triple = this.#asserted.get(key);
      if (triple !== undefined) this.#store(...triple);
    }
    engine.run();
    for (const fact of this.#triples.facts()) {
      if (fact.bornAt < since) continue;
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
  inconsistencies(): Inconsistency[] {
    if (!this.#ran) this.run();
    const terms = this.#engine.terms;
    const none = terms.id(NONE);
    const reports: Inconsistency[] = [];
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
    this.#asserted.set(tripleKey(subject, predicate, object), [
      subject,
      predicate,
      object,
    ]);
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
