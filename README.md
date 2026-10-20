# @wazoo/reasoner

An OWL 2 RL reasoner over RDF/JS quad stores, built alongside
[`@wazoo/sparql-engine`](https://github.com/wazootech/sparql-engine).

**Status: in development, unreleased.** The OWL 2 RL ruleset, the semi-naive
engine, `owl:sameAs` as a union-find, and incremental additions (`extend`) work,
and `deno task test:parity <file.nt ...>` compares the closure with the Wiki's
current engine. The W3C conformance suite and CI are not wired up yet. The plan
is [wazootech/reasoner#1](https://github.com/wazootech/reasoner/issues/1); the
evidence for it is in
[wazootech/wiki#414](https://github.com/wazootech/wiki/issues/414).

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

A separate package that depends on `@wazoo/sparql-engine`'s term model and
store. Querying and reasoning have different specifications, test suites, and
release cadences, so neither forces a release of the other.
