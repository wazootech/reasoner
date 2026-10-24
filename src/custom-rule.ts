import type { Term } from "@rdfjs/types";
import { dataFactory } from "@wazoo/sparql-engine/term";
import { INCONSISTENCY, NONE, OWL2RL_RULES, TRIPLE } from "@/owl2rl/rules.ts";
import { atom, type Rule, type RuleArgument, Variable } from "@/rule.ts";

/**
 * TriplePattern is one `[subject, predicate, object]` pattern of a custom
 * rule. Each position is an RDF/JS term (a constant) or a {@link Variable}.
 */
export type TriplePattern = readonly [
  subject: RuleArgument,
  predicate: RuleArgument,
  object: RuleArgument,
];

/**
 * CustomRule is a Datalog-style rule over triples: for every way the `body`
 * patterns match the closure together, each `head` pattern is derived with the
 * same variable bindings, and `inconsistent` (if given) reports an
 * inconsistency.
 *
 * ```ts
 * const { x, y, z } = variables();
 * const grandparent: CustomRule = {
 *   name: "grandparent",
 *   body: [[x, parent, y], [y, parent, z]],
 *   head: [[x, grandparent, z]],
 * };
 * ```
 *
 * A rule is valid when its `name` is non-empty and unique, `body` has at least
 * one pattern, it has a `head` pattern or an `inconsistent` list, every
 * variable in `head` or `inconsistent` occurs in `body`, and every constant
 * predicate in `head` is a named node.
 */
export interface CustomRule {
  /**
   * name identifies the rule. It is reported as `Inconsistency.rule` and must
   * differ from every OWL 2 RL rule name and every other custom rule name.
   */
  readonly name: string;
  /** body is the premises; all must match for the rule to fire. */
  readonly body: readonly TriplePattern[];
  /** head is the triples derived for each match. May be empty. */
  readonly head?: readonly TriplePattern[];
  /**
   * inconsistent, when present, reports an {@link Inconsistency} named after
   * the rule for each match, with these (at most five) terms as its `terms`.
   */
  readonly inconsistent?: readonly RuleArgument[];
}

/** RuleOptions are the custom rules an engine evaluates beside OWL 2 RL. */
export interface RuleOptions {
  /** rules are custom rules to evaluate alongside the OWL 2 RL rules. */
  readonly rules?: readonly CustomRule[];
}

const RESERVED = new Set(OWL2RL_RULES.map((rule) => rule.name));

function isArgument(value: unknown): value is RuleArgument {
  return value instanceof Variable ||
    (typeof value === "object" && value !== null &&
      typeof (value as Term).termType === "string" &&
      (value as Term).termType !== "Quad" &&
      (value as Term).termType !== "DefaultGraph");
}

/**
 * compileCustomRule validates `rule` and lowers it onto the engine's internal
 * rule type. It throws an `Error` naming the rule and the problem.
 */
export function compileCustomRule(
  rule: CustomRule,
  taken: ReadonlySet<string>,
): Rule {
  const fail = (message: string): never => {
    throw new Error(`Invalid rule ${JSON.stringify(rule.name)}: ${message}`);
  };
  if (typeof rule.name !== "string" || rule.name === "") {
    fail("name must be a non-empty string");
  }
  if (RESERVED.has(rule.name)) fail("name is an OWL 2 RL rule name");
  if (taken.has(rule.name)) fail("name is already registered");
  if (!Array.isArray(rule.body) || rule.body.length === 0) {
    fail("body needs at least one pattern");
  }
  const head = rule.head ?? [];
  const inconsistent = rule.inconsistent;
  if (head.length === 0 && inconsistent === undefined) {
    fail("needs a head pattern or an inconsistent list");
  }
  const check = (pattern: TriplePattern, where: string) => {
    if (!Array.isArray(pattern) || pattern.length !== 3) {
      fail(`${where} pattern must be [subject, predicate, object]`);
    }
    for (const arg of pattern) {
      if (!isArgument(arg)) fail(`${where} pattern has an invalid term`);
    }
  };
  const bound = new Set<Variable>();
  for (const pattern of rule.body) {
    check(pattern, "body");
    for (const arg of pattern) if (arg instanceof Variable) bound.add(arg);
  }
  const needBound = (arg: RuleArgument) => {
    if (arg instanceof Variable && !bound.has(arg)) {
      fail(`unbound head variable ?${arg.name} (it must occur in the body)`);
    }
  };
  for (const pattern of head) {
    check(pattern, "head");
    pattern.forEach(needBound);
    const predicate = pattern[1];
    if (
      !(predicate instanceof Variable) && predicate.termType !== "NamedNode"
    ) {
      fail("a constant head predicate must be a named node");
    }
  }
  if (inconsistent !== undefined) {
    if (!Array.isArray(inconsistent) || inconsistent.length > 5) {
      fail("inconsistent takes at most five terms");
    }
    for (const arg of inconsistent) {
      if (!isArgument(arg)) fail("inconsistent has an invalid term");
      needBound(arg);
    }
  }
  const heads = head.map(([s, p, o]) => atom(TRIPLE, s, p, o));
  if (inconsistent !== undefined) {
    const padded = [...inconsistent];
    while (padded.length < 5) padded.push(NONE);
    heads.push(
      atom(INCONSISTENCY, dataFactory.literal(rule.name), ...padded),
    );
  }
  return {
    name: rule.name,
    body: rule.body.map(([s, p, o]) => atom(TRIPLE, s, p, o)),
    head: heads,
  };
}
