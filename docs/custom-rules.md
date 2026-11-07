# Custom rules: what works

A factual matrix for the custom Datalog-rule layer (`CustomRule`), verified by
probe against 0.4.0 (`probes.ts`, 28 scenarios, all green as of 2026-11-07).
Where a row says "rejected", that is registration-time validation with the
message the caller sees.

The OWL 2 RL ruleset has its own conformance story (`test/w3c`, 88/90 with two
documented gaps in `known-gaps.json`); this page covers only the custom layer.

## Body and head patterns

| Capability | Status |
|---|---|
| All-constant patterns (ground rule) | works |
| Variables shared across patterns (join) | works |
| Same variable twice in one pattern (self-join) | works |
| Chained rules (rule 2 consumes rule 1's head) | works |
| Recursive rules (rule consumes own head, converges) | works |
| Plain literals in body and head | works |
| Typed literals in body (`"18"^^xsd:integer` joins) | works |
| Language-tagged literals in body | works |
| Blank nodes as constant patterns | works |
| Head-only variables (existential) | rejected: `unbound head variable ?z (it must occur in the body)` |
| Fresh predicate variable in head | rejected (same message) |
| Bare strings or IRIs as pattern terms | rejected: `body pattern has an invalid term` |
| Empty head without an `inconsistent` list | rejected: `needs a head pattern or an inconsistent list` |

## Interaction with OWL 2 RL

| Capability | Status |
|---|---|
| OWL 2 RL materialization feeds custom rules (`rdfs:subClassOf` type derivation joins a custom pattern) | works |
| Custom derivation in `closure("application")` view | works |
| Rule named like an OWL 2 RL rule | rejected: `name is an OWL 2 RL rule name` |
| Duplicate rule name (including the same object twice) | rejected: `name is already registered` |

## Incremental (delta) path

| Capability | Status |
|---|---|
| `extend()` fires custom rules on new quads | works (recursive closure continues correctly) |
| `retract()` undoes custom-rule derivations, keeps derivable-from-remaining facts | works |
| `retract()` of a derived-only triple | no-op, returns `[]` |
| `extend()` with late OWL axioms (subclass axiom arrives after run) | works |
| `retract()` of asserted triples also removes OWL-entailed consequences | works |

## Graph modes

| Capability | Status |
|---|---|
| `per-graph` (default): custom rules see all graphs | works |
| `graphs: "union"` with custom rules | works |

## Inconsistency reporting

| Capability | Status |
|---|---|
| `inconsistent` rule without a head (assert nothing, report only) | works |
| `inconsistent` with more than five terms | rejected: `inconsistent takes at most five` |

## Known gaps (filed)

- **No negation.** Body premises are positive only; a pattern cannot require a
  fact's absence. Proposal and motivation: #33 (stratified negation as failure).
- **No disequality.** Variables cannot be required to bind distinct terms, and
  symmetric patterns report both binding orders. #34, with the workaround.
- **Term contract enforced late.** Plain `{ termType, value }` objects pass
  `add()`/`run()` and crash only inside `closure()` (#35).
- **Error messages do not locate the offending pattern.** `body pattern has an
  invalid term` names neither the index nor the position (#36).

## Semantics notes

- Custom rules join the semi-naive evaluation with the OWL 2 RL ruleset and
  share its monotonicity: a fact, once derived, stays derived unless its
  support is retracted. There is no rule firing order dependence.
- Rules are global, not per-graph: the pattern language has no graph position;
  graph scoping follows the same rules as OWL 2 RL entailment (per-graph mode
  lists per graph, entailment sees every graph).
