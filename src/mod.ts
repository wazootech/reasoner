/**
 * @module
 * An OWL 2 RL reasoner over RDF/JS terms.
 *
 * {@link Reasoner} materializes the OWL 2 RL/RDF closure of a set of triples
 * semi-naively, through hash-indexed joins, with `owl:sameAs` kept as a
 * union-find rather than as copied triples. {@link Reasoner.extend} reasons
 * about added triples against a closure that is already computed.
 */
export {
  type ClosureView,
  DERIVED_GRAPH,
  type GraphMode,
  type Inconsistency,
  Reasoner,
  type ReasonerOptions,
  type RetractOptions,
  type Triple,
} from "@/reasoner.ts";
export { type CustomRule, type TriplePattern } from "@/custom-rule.ts";
export { Engine, type EngineOptions, type EngineStatistics } from "@/engine.ts";
export {
  atom,
  type AtomPattern,
  bind,
  type BodyPattern,
  type BuiltinContext,
  type BuiltinPattern,
  filter,
  type Rule,
  type RuleArgument,
  Variable,
  variables,
} from "@/rule.ts";
export { AXIOMS, COMPLEMENT_PREFIX, OWL2RL_RULES } from "@/owl2rl/rules.ts";
