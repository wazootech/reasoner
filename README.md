# @wazoo/reasoner

An OWL 2 RL reasoner over RDF/JS quad stores, built alongside
[`@wazoo/sparql-engine`](https://github.com/wazootech/sparql-engine).

**Status: 0.1.0, published to JSR (2026-10-21).** The OWL 2 RL ruleset, the
semi-naive engine, `owl:sameAs` as a union-find, and incremental additions
(`extend`) work. Retraction is not implemented yet, and the Worlds integration
has not started. The Wiki's switch from `rdfjs-inference-engine` to this package
is pending merge in
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

- **W3C OWL 2 RL suite** (`deno task test:w3c`): 81 of 90 pass. Four have no
  RDF/XML premise and one imports another ontology. Four conclusions are not
  entailed: `WebOnt-equivalentClass-008-Direct`, `WebOnt-I4.6-005-Direct`,
  `WebOnt-I5.26-010`, and `WebOnt-I5.5-005`. `rdfjs-inference-engine` fails the
  same four, so they are known gaps, not regressions.
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
- **Incremental.** Given a closure and a Δ, derive only what the Δ adds (and,
  later, retract what a deletion removes). This shares its "what does this
  change touch" question with the scoped SHACL validation planned for Worlds
  ([worlds-sdk-ts#151](https://github.com/wazootech/worlds-sdk-ts/issues/151)).
- **Gated like `sparql-engine`.** Done means the W3C OWL 2 RL conformance tests
  pass in CI, and the closure matches the Wiki's current engine triple for
  triple on its parity corpora before the Wiki switches over.

## Relationship to `sparql-engine`

A separate package that depends on `@wazoo/sparql-engine`'s term model. Querying
and reasoning have different specifications, test suites, and release cadences,
so neither forces a release of the other.
