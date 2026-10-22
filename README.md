# @wazoo/reasoner

An OWL 2 RL reasoner over RDF/JS quad stores, built alongside
[`@wazoo/sparql-engine`](https://github.com/wazootech/sparql-engine).

**Status: 0.1.0, published to JSR (2026-10-21).** The OWL 2 RL ruleset, the
semi-naive engine, and `owl:sameAs` as a union-find work. Incremental additions
(`extend`) work but are known to miss some derivations when `owl:sameAs` arrives
late ([#8](https://github.com/wazootech/reasoner/issues/8); the failure classes
are listed by `test:differential`). `retract` removes asserted triples by
recomputing their connected component, and the Worlds integration has not
started. The Wiki switched from `rdfjs-inference-engine` to this package in
[wazootech/wiki#418](https://github.com/wazootech/wiki/pull/418). The plan is
[wazootech/reasoner#1](https://github.com/wazootech/reasoner/issues/1); the
evidence for it is in
[wazootech/wiki#414](https://github.com/wazootech/wiki/issues/414).

## Usage

```ts
import { Reasoner } from "@wazoo/reasoner";

const reasoner = new Reasoner();
reasoner.add(quads); // any RDF/JS triples; the graph term is ignored
reasoner.run();
for (const quad of reasoner.closure("application")) store.add(quad);
reasoner.inconsistencies(); // [{ rule: "cax-dw", terms: [...] }, ...]

// Later: reason about a change against the closure already computed.
const added = reasoner.extend(moreQuads, "application");

// Or take asserted triples back; the result is what is no longer entailed.
const removed = reasoner.retract(goneQuads, "application");
```

`closure("complete")` lists every entailed triple. `"application"` leaves out
what a graph store has no use for: literal subjects, reflexive `owl:sameAs`,
complement-class skolems, and types whose class is a blank node.

## Testing

- `deno task ci`: format, lint, type-check, unit tests.
- `deno task test:parity`: the closure against the Wiki's current engine
  (`rdfjs-inference-engine`), triple for triple, on the corpora in
  `test/parity/corpora/`. Every difference must be a documented divergence.
- `deno task test:w3c`: the W3C OWL 2 RL test cases (approved and proposed),
  fetched from w3.org into `.cache/`. A test in `test/w3c/expected-pass.json`
  that fails is a regression; `deno task test:w3c:update` records new passes.
- `deno task bench`: closure time and memory on synthetic graphs
  (`--sizes 1e3,1e4,1e5 --profile plain|equality`).

## Conformance

- **W3C OWL 2 RL suite** (`deno task test:w3c`): 87 of 90 pass. The harness
  reads tests given in OWL functional syntax (a subset, `functional-syntax.ts`),
  follows `owl:imports`, and ignores annotations in the conclusion of
  Direct-Semantics tests. Three conclusions are not entailed, each with its
  reason in `test/w3c/known-gaps.json`:
  `New-Feature-ObjectPropertyChain-BJP-002` (no RL rule concludes a
  `propertyChainAxiom`), and `WebOnt-I5.26-010` and `WebOnt-I5.5-005` (bare
  anonymous class expressions, which the rules never create).
- **Parity with `rdfjs-inference-engine`** (`deno task test:parity`): identical
  closures on `bench-1e3`, `docs`, `micro`, and `owl-nosame`. On `owl` this
  package derives two extra triples, a documented divergence (`eq-rep` applied
  to an ontology triple).

## Why

The Wiki CLI and Worlds need OWL 2 RL materialization that scales with the
graph. The engine the Wiki uses today, `rdfjs-inference-engine` over Eyeling,
grows quadratically even on graphs that derive nothing: Eyeling evaluates
`owl:sameAs` as a builtin that scans every fact, and the equality rules call it
once per triple. It also re-reasons over all of its input on every call, while
Worlds needs to reason about a change (Δ) against an existing closure.

## Goals

- **Linear in the data where OWL 2 RL allows it.** The rules are compiled to
  indexed joins, not interpreted as N3 text. Evaluation is semi-naive, and
  `owl:sameAs` is handled with a union-find of representatives instead of
  copying triples.
- **Incremental.** Given a closure and a Δ, derive only what the Δ adds (and
  retract what a deletion removes). `retract` re-derives only the connected
  component of the deleted triple, but it finds that component with one pass
  over the asserted triples, so its cost is linear in the graph plus the
  component, and a component past `maxScope` is recomputed whole. This shares
  its "what does this change touch" question with the scoped SHACL validation
  planned for Worlds
  ([worlds-sdk-ts#151](https://github.com/wazootech/worlds-sdk-ts/issues/151)).
- **Gated like `sparql-engine`.** Done means the W3C OWL 2 RL conformance tests
  pass in CI, and the closure matches the Wiki's current engine triple for
  triple on its parity corpora before the Wiki switches over.

## Relationship to `sparql-engine`

A separate package that depends on `@wazoo/sparql-engine`'s term model. Querying
and reasoning have different specifications, test suites, and release cadences,
so neither forces a release of the other.
