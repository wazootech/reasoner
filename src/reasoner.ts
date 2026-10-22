import type { NamedNode, Quad, Term } from "@rdfjs/types";
import { dataFactory } from "@wazoo/sparql-engine/term";
import { Engine, type EngineStatistics } from "@/engine.ts";
import type { Fact, Relation } from "@/relation.ts";
import { factKey } from "@/relation.ts";
import {
  AXIOMS,
  COMPLEMENT_PREFIX,
  INCONSISTENCY,
  NONE,
  OWL2RL_RULES,
  RELATIONS,
  TRIPLE,
} from "@/owl2rl/rules.ts";
import { OWL, RDF } from "@/owl2rl/vocabulary.ts";

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
 * evaluating only the rules the new facts can reach.
 */
export class Reasoner {
  #engine: Engine;
  #triples: Relation;
  #ran = false;

  constructor() {
    this.#engine = new Engine(OWL2RL_RULES, {
      equalityRelation: TRIPLE,
      sameAs: OWL.sameAs,
      relations: RELATIONS,
      contentTerm: (term) => term.termType === "Literal",
    });
    this.#triples = this.#engine.relation(TRIPLE);
    for (const [subject, predicate, object] of AXIOMS) {
      this.#assert(subject, predicate, object);
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
    if (predicate.termType !== "NamedNode") return undefined;
    const subject = terms.term(s);
    const object = terms.term(o);
    if (view === "application") {
      if (subject.termType === "Literal") return undefined;
      if (s === o && predicate.equals(OWL.sameAs)) return undefined;
      if (isSkolem(subject) || isSkolem(predicate) || isSkolem(object)) {
        return undefined;
      }
      if (predicate.equals(RDF.type) && object.termType === "BlankNode") {
        return undefined;
      }
    }
    return dataFactory.quad(
      subject as Quad["subject"],
      predicate as NamedNode,
      object as Quad["object"],
    );
  }
}
