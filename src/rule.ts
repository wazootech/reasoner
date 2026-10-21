import type { Term } from "@rdfjs/types";

/** Variable is a named rule variable. */
export class Variable {
  readonly name: string;
  constructor(name: string) {
    this.name = name;
  }
}

/** RuleArgument is a constant term or a rule variable. */
export type RuleArgument = Term | Variable;

/** AtomPattern matches or produces facts of one relation. */
export interface AtomPattern {
  readonly kind: "atom";
  readonly relation: string;
  readonly args: readonly RuleArgument[];
}

/**
 * BuiltinContext is what a builtin may read: the terms behind ids, and the
 * current equality classes.
 */
export interface BuiltinContext {
  term(id: number): Term;
  id(term: Term): number;
  find(id: number): number;
  members(root: number): readonly number[];
}

/**
 * BuiltinPattern computes bindings instead of matching stored facts. It runs
 * once all of its `inputs` are bound and yields one tuple of `outputs` values
 * per solution; a filter has no outputs and yields one empty tuple to pass.
 */
export interface BuiltinPattern {
  readonly kind: "builtin";
  readonly name: string;
  readonly inputs: readonly Variable[];
  readonly outputs: readonly Variable[];
  readonly run: (
    inputs: readonly number[],
    context: BuiltinContext,
  ) => Iterable<readonly number[]>;
}

/** BodyPattern is one premise of a rule. */
export type BodyPattern = AtomPattern | BuiltinPattern;

/** Rule derives every head atom for each solution of its body. */
export interface Rule {
  readonly name: string;
  readonly body: readonly BodyPattern[];
  readonly head: readonly AtomPattern[];
}

/** atom builds an {@link AtomPattern}. */
export function atom(
  relation: string,
  ...args: readonly RuleArgument[]
): AtomPattern {
  return { kind: "atom", relation, args };
}

const PASS: readonly (readonly number[])[] = [[]];
const FAIL: readonly (readonly number[])[] = [];

/** filter builds a builtin that keeps a solution when `test` holds. */
export function filter(
  name: string,
  inputs: readonly Variable[],
  test: (inputs: readonly number[], context: BuiltinContext) => boolean,
): BuiltinPattern {
  return {
    kind: "builtin",
    name,
    inputs,
    outputs: [],
    run: (values, context) => test(values, context) ? PASS : FAIL,
  };
}

/** bind builds a builtin that binds `outputs` from `inputs`. */
export function bind(
  name: string,
  inputs: readonly Variable[],
  outputs: readonly Variable[],
  run: BuiltinPattern["run"],
): BuiltinPattern {
  return { kind: "builtin", name, inputs, outputs, run };
}

/**
 * variables returns a proxy whose every property is the variable of that
 * name, so rules read like their tables: `const { x, p, y } = variables()`.
 */
export function variables(): Record<string, Variable> {
  const cache = new Map<string, Variable>();
  return new Proxy({}, {
    get(_target, name) {
      if (typeof name !== "string") return undefined;
      let variable = cache.get(name);
      if (variable === undefined) {
        variable = new Variable(name);
        cache.set(name, variable);
      }
      return variable;
    },
  }) as Record<string, Variable>;
}
