# @wazoo/reasoner

An OWL 2 RL reasoner over RDF/JS quad stores, built alongside
[`@wazoo/sparql-engine`](https://github.com/wazootech/sparql-engine).

**Status: in development, unreleased.** The OWL 2 RL ruleset, the semi-naive
engine, `owl:sameAs` as a union-find, and incremental additions (`extend`) work.
Retraction is not implemented yet. The plan is
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
