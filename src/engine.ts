import type { Term } from "@rdfjs/types";
import { Equality } from "@/equality.ts";
import { type Fact, Relation } from "@/relation.ts";
import {
  type AtomPattern,
  type BuiltinContext,
  type BuiltinPattern,
  type Rule,
  Variable,
} from "@/rule.ts";
import { TermDictionary } from "@/term-dictionary.ts";

/**
 * A compiled argument: a term id when `>= 0`, else variable slot `-arg - 1`.
 */
type CompiledArgument = number;

interface CompiledAtom {
  readonly kind: "atom";
  readonly relation: Relation;
  readonly args: readonly CompiledArgument[];
}

interface CompiledBuiltin {
  readonly kind: "builtin";
  readonly name: string;
  readonly inputs: readonly number[];
  readonly outputs: readonly number[];
  readonly run: BuiltinPattern["run"];
}

type CompiledStep = CompiledAtom | CompiledBuiltin;

interface CompiledRule {
  readonly name: string;
  readonly slots: number;
  readonly head: readonly CompiledAtom[];
  /** plans[i] joins the rest of the body after seeding body atom `atoms[i]`. */
  readonly seeds: readonly Seed[];
}

interface Seed {
  readonly atom: CompiledAtom;
  readonly plan: readonly CompiledStep[];
  /**
   * keyColumn is a column the seed atom fixes to a constant (its predicate,
   * when it has one), or -1. A round only offers the seed the delta facts
   * that hold that constant there.
   */
  readonly keyColumn: number;
}

/** EngineOptions configure the relation that carries `owl:sameAs`. */
export interface EngineOptions {
  /** equalityRelation is the arity-3 relation whose sameAs facts merge terms. */
  readonly equalityRelation: string;
  /** sameAs is the predicate that states two terms are equal. */
  readonly sameAs: Term;
  /** relations declares each relation the rules use, with its arity. */
  readonly relations: Readonly<Record<string, number>>;
}

/** EngineStatistics summarize the work of the runs so far. */
export interface EngineStatistics {
  rounds: number;
  derivations: number;
  merges: number;
}

const UNBOUND = -1;

/**
 * Engine evaluates a set of rules to a fixpoint, semi-naively: each round
 * joins only the facts the previous round added against everything stored,
 * through hash indexes chosen per join step. Facts whose relation is the
 * equality relation and whose predicate is `sameAs` merge their subject and
 * object instead of being stored as-is (see {@link Equality}).
 */
export class Engine {
  readonly terms: TermDictionary = new TermDictionary();
  readonly equality: Equality = new Equality();
  readonly statistics: EngineStatistics = {
    rounds: 0,
    derivations: 0,
    merges: 0,
  };
  #relations = new Map<string, Relation>();
  #rules: CompiledRule[];
  #equalityRelation: Relation;
  #sameAs: number;
  #clock = 0;
  #delta = new Map<Relation, Fact[]>();
  #absorbed: number[] = [];
  #context: BuiltinContext;

  constructor(rules: readonly Rule[], options: EngineOptions) {
    for (const [name, arity] of Object.entries(options.relations)) {
      this.#relations.set(name, new Relation(name, arity));
    }
    this.#equalityRelation = this.relation(options.equalityRelation);
    this.#sameAs = this.terms.id(options.sameAs);
    this.#context = {
      term: (id) => this.terms.term(id),
      id: (term) => this.terms.id(term),
      find: (id) => this.equality.find(id),
      members: (root) => this.equality.members(root),
    };
    this.#rules = rules.map((rule) => this.#compile(rule));
  }

  /** clock is the tick the next stored fact will carry. */
  get clock(): number {
    return this.#clock;
  }

  /**
   * tick advances the clock and returns the new tick, so every fact stored
   * from now on is younger than every fact stored before.
   */
  tick(): number {
    return ++this.#clock;
  }

  /** relation returns the declared relation called `name`. */
  relation(name: string): Relation {
    const relation = this.#relations.get(name);
    if (relation === undefined) throw new Error(`Unknown relation ${name}`);
    return relation;
  }

  /** relations yields every declared relation. */
  relations(): IterableIterator<Relation> {
    return this.#relations.values();
  }

  /**
   * add stores a fact of `relation` for the next {@link Engine.run} and
   * returns `true` if it was new.
   */
  add(relation: string, args: readonly number[]): boolean {
    return this.#store(this.relation(relation), args);
  }

  /** run evaluates the rules until no round derives a new fact. */
  run(): void {
    this.#settle();
    while (this.#delta.size > 0) {
      this.statistics.rounds++;
      const delta = this.#delta;
      const grouped = new Map<Relation, Map<number, Fact[]>[]>();
      this.#delta = new Map();
      this.#clock++;
      for (const rule of this.#rules) {
        const binding = new Array<number>(rule.slots).fill(UNBOUND);
        for (const seed of rule.seeds) {
          const facts = this.#seedFacts(delta, grouped, seed);
          if (facts === undefined) continue;
          for (const fact of facts) {
            if (fact.diedAt !== Infinity) continue;
            const bound = this.#unify(seed.atom, fact.args, binding);
            if (bound === null) continue;
            this.#join(rule, seed.plan, 0, binding);
            for (const slot of bound) binding[slot] = UNBOUND;
          }
        }
      }
      this.#settle();
    }
  }

  /** seedFacts returns the delta facts `seed` can match, grouping on demand. */
  #seedFacts(
    delta: Map<Relation, Fact[]>,
    grouped: Map<Relation, Map<number, Fact[]>[]>,
    seed: Seed,
  ): readonly Fact[] | undefined {
    const relation = seed.atom.relation;
    const facts = delta.get(relation);
    if (facts === undefined || seed.keyColumn < 0) return facts;
    let columns = grouped.get(relation);
    if (columns === undefined) {
      columns = [];
      grouped.set(relation, columns);
    }
    let groups = columns[seed.keyColumn];
    if (groups === undefined) {
      groups = new Map();
      for (const fact of facts) {
        const id = fact.args[seed.keyColumn]!;
        const group = groups.get(id);
        if (group === undefined) groups.set(id, [fact]);
        else group.push(fact);
      }
      columns[seed.keyColumn] = groups;
    }
    const constant = this.equality.find(seed.atom.args[seed.keyColumn]!);
    return groups.get(constant);
  }

  #store(relation: Relation, args: readonly number[]): boolean {
    const equality = this.equality;
    const canonical = args.map((id) => equality.find(id));
    if (
      relation === this.#equalityRelation &&
      canonical[1] === equality.find(this.#sameAs) &&
      canonical[0] !== canonical[2]
    ) {
      const absorbed = equality.union(
        canonical[0]!,
        canonical[2]!,
        this.#clock,
      );
      if (absorbed !== undefined) {
        this.statistics.merges++;
        this.#absorbed.push(absorbed);
      }
      const root = equality.find(canonical[0]!);
      canonical[0] = root;
      canonical[2] = root;
      canonical[1] = equality.find(canonical[1]!);
    }
    const fact = relation.insert(canonical, this.#clock);
    if (fact === undefined) return false;
    this.statistics.derivations++;
    const pending = this.#delta.get(relation);
    if (pending === undefined) this.#delta.set(relation, [fact]);
    else pending.push(fact);
    return true;
  }

  /**
   * settle renames every fact that mentions a term absorbed by a merge. The
   * renamed facts join the next round's delta, so rules see the merged class
   * as one term.
   */
  #settle(): void {
    while (this.#absorbed.length > 0) {
      const absorbed = this.#absorbed.pop()!;
      for (const relation of this.#relations.values()) {
        for (let column = 0; column < relation.arity; column++) {
          for (const fact of relation.column(column, absorbed)) {
            if (fact.diedAt !== Infinity) continue;
            relation.retire(fact, this.#clock);
            this.#store(relation, fact.args);
          }
        }
        relation.forget(absorbed);
      }
    }
  }

  #join(
    rule: CompiledRule,
    plan: readonly CompiledStep[],
    step: number,
    binding: number[],
  ): void {
    if (step === plan.length) {
      for (const head of rule.head) {
        const args = head.args.map((arg) =>
          arg >= 0 ? arg : binding[-arg - 1]!
        );
        this.#store(head.relation, args);
      }
      return;
    }
    const current = plan[step]!;
    if (current.kind === "builtin") {
      const inputs = current.inputs.map((slot) => binding[slot]!);
      for (const outputs of current.run(inputs, this.#context)) {
        const bound: number[] = [];
        let ok = true;
        for (let index = 0; index < current.outputs.length; index++) {
          // Outputs stay as given, so a builtin can name one member of an
          // equality class (a literal, say); lookups and heads canonicalize.
          const slot = current.outputs[index]!;
          const value = outputs[index]!;
          if (binding[slot] === UNBOUND) {
            binding[slot] = value;
            bound.push(slot);
          } else if (
            this.equality.find(binding[slot]!) !== this.equality.find(value)
          ) {
            ok = false;
            break;
          }
        }
        if (ok) this.#join(rule, plan, step + 1, binding);
        for (const slot of bound) binding[slot] = UNBOUND;
      }
      return;
    }
    let mask = 0;
    const values: number[] = [];
    for (let column = 0; column < current.args.length; column++) {
      const arg = current.args[column]!;
      const value = arg >= 0 ? arg : binding[-arg - 1]!;
      if (value === UNBOUND) continue;
      mask |= 1 << column;
      values.push(this.equality.find(value));
    }
    const facts = current.relation.lookup(mask, values);
    for (let index = 0; index < facts.length; index++) {
      const fact = facts[index]!;
      if (fact.diedAt !== Infinity) continue;
      const bound = this.#unify(current, fact.args, binding);
      if (bound === null) continue;
      this.#join(rule, plan, step + 1, binding);
      for (const slot of bound) binding[slot] = UNBOUND;
    }
  }

  /**
   * unify binds `atom`'s free variables to `args`, and returns the slots it
   * bound, or `null` (binding nothing) if the fact does not match.
   */
  #unify(
    atom: CompiledAtom,
    args: readonly number[],
    binding: number[],
  ): number[] | null {
    const bound: number[] = [];
    for (let column = 0; column < atom.args.length; column++) {
      const arg = atom.args[column]!;
      const value = args[column]!;
      if (arg >= 0) {
        if (this.equality.find(arg) !== value) return undo(bound, binding);
        continue;
      }
      const slot = -arg - 1;
      if (binding[slot] === UNBOUND) {
        binding[slot] = value;
        bound.push(slot);
      } else if (this.equality.find(binding[slot]!) !== value) {
        return undo(bound, binding);
      }
    }
    return bound;
  }

  #compile(rule: Rule): CompiledRule {
    const slots = new Map<Variable, number>();
    const slot = (variable: Variable): number => {
      let index = slots.get(variable);
      if (index === undefined) {
        index = slots.size;
        slots.set(variable, index);
      }
      return index;
    };
    const compileAtom = (pattern: AtomPattern): CompiledAtom => {
      const relation = this.relation(pattern.relation);
      if (pattern.args.length !== relation.arity) {
        throw new Error(
          `Rule ${rule.name}: ${pattern.relation} takes ${relation.arity} arguments`,
        );
      }
      return {
        kind: "atom",
        relation,
        args: pattern.args.map((arg) =>
          arg instanceof Variable ? -slot(arg) - 1 : this.terms.id(arg)
        ),
      };
    };
    const body: CompiledStep[] = rule.body.map((pattern) =>
      pattern.kind === "atom" ? compileAtom(pattern) : {
        kind: "builtin",
        name: pattern.name,
        inputs: pattern.inputs.map(slot),
        outputs: pattern.outputs.map(slot),
        run: pattern.run,
      }
    );
    const head = rule.head.map(compileAtom);
    const atoms = body.filter((step): step is CompiledAtom =>
      step.kind === "atom"
    );
    if (atoms.length === 0) {
      throw new Error(`Rule ${rule.name} has no body atom to seed from`);
    }
    const seeds = atoms.map((seed): Seed => {
      const constants = seed.args.flatMap((arg, column) =>
        arg >= 0 ? [column] : []
      );
      return {
        atom: seed,
        plan: plan(rule.name, seed, body.filter((step) => step !== seed)),
        keyColumn: constants.includes(1) ? 1 : constants[0] ?? -1,
      };
    });
    const bodyVariables = new Set<number>();
    for (const step of body) {
      for (const variable of variablesOf(step)) bodyVariables.add(variable);
    }
    for (const atom of head) {
      for (const arg of atom.args) {
        if (arg < 0 && !bodyVariables.has(-arg - 1)) {
          throw new Error(`Rule ${rule.name}: a head variable is unbound`);
        }
      }
    }
    return { name: rule.name, slots: slots.size, head, seeds };
  }
}

function undo(bound: number[], binding: number[]): null {
  for (const slot of bound) binding[slot] = UNBOUND;
  return null;
}

function variablesOf(step: CompiledStep): number[] {
  if (step.kind === "builtin") return [...step.inputs, ...step.outputs];
  return step.args.filter((arg) => arg < 0).map((arg) => -arg - 1);
}

/**
 * plan orders the remaining body after a seed: a builtin as soon as its
 * inputs are bound, otherwise the atom with the most bound columns (ties keep
 * the rule's written order, so rules list their schema atoms first).
 */
function plan(
  name: string,
  seed: CompiledAtom,
  rest: CompiledStep[],
): CompiledStep[] {
  const bound = new Set(variablesOf(seed));
  const ordered: CompiledStep[] = [];
  const remaining = rest.slice();
  while (remaining.length > 0) {
    let chosen = remaining.findIndex((step) =>
      step.kind === "builtin" && step.inputs.every((input) => bound.has(input))
    );
    if (chosen === -1) {
      let best = -1;
      for (let index = 0; index < remaining.length; index++) {
        const step = remaining[index]!;
        if (step.kind !== "atom") continue;
        const score = step.args.filter((arg) => arg >= 0 || bound.has(-arg - 1))
          .length;
        if (score > best) {
          best = score;
          chosen = index;
        }
      }
    }
    if (chosen === -1) {
      throw new Error(`Rule ${name}: a builtin's inputs are never bound`);
    }
    const [step] = remaining.splice(chosen, 1);
    ordered.push(step!);
    for (const variable of variablesOf(step!)) bound.add(variable);
  }
  return ordered;
}
