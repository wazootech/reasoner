# @wazoo/reasoner

An OWL 2 RL reasoner over RDF/JS quad stores, built alongside
[`@wazoo/sparql-engine`](https://github.com/wazootech/sparql-engine).

**Status: 0.3.0.** The OWL 2 RL ruleset, the semi-naive engine, `owl:sameAs` as
a union-find, incremental additions (`extend`) and retraction (`retract`) work,
and `deno task test:differential` finds no difference between `extend` or
`retract` and a fresh run on 5,000 random graphs. The Worlds integration has not
started. The Wiki switched from `rdfjs-inference-engine` to this package in
[wazootech/wiki#418](https://github.com/wazootech/wiki/pull/418). The plan is
[wazootech/reasoner#1](https://github.com/wazootech/reasoner/issues/1); the
evidence for it is in
[wazootech/wiki#414](https://github.com/wazootech/wiki/issues/414).

## Usage

```ts
import { Reasoner } from "@wazoo/reasoner";

const reasoner = new Reasoner();
reasoner.add(quads); // RDF/JS quads; the graph term names the graph (see below)
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

## Named graphs

`new Reasoner()` reasons per graph by default;
`new Reasoner({ graphs: "union" })` merges every graph into one closure listed
in the default graph, as it did when the graph term was ignored. A caller that
uses only the default graph sees no difference.

In per-graph mode entailment still sees every graph, so a rule can join a
subclass axiom in one graph with a typed instance in another. The graphs decide
where a triple is _listed_: each entailed triple is in every graph that asserts
it or whose own closure entails it, in the default graph when it is an axiomatic
triple, and in `DERIVED_GRAPH` (`https://wazoo.dev/ns/reasoner#derived`) when
only a combination of graphs entails it. `has(s, p, o, graph?)` takes the graph
too, `inconsistencies()` names the graph (or the derived graph) whose closure
violates each rule, and `extend` and `retract` return quads with their graphs. A
triple asserted in two graphs stays asserted until it is retracted from both.

With more than one graph, per-graph mode also computes the closure of each graph
alone (lazily, once per change) and `extend`/`retract` diff the listings, so
they cost a pass over the closure instead of just the change. Use one graph, or
`"union"`, where that matters.

## Custom rules

Register Datalog-style rules over triple patterns, in the constructor or with
`addRule`. A pattern is `[subject, predicate, object]`; each position is an
RDF/JS term or a variable from `variables()`.

```ts
import { Reasoner, variables } from "@wazoo/reasoner";

const { x, y, z } = variables();
const reasoner = new Reasoner({
  rules: [
    {
      name: "grandparent",
      body: [[x, parent, y], [y, parent, z]],
      head: [[x, grandparent, z]],
    },
    {
      name: "no-self-parent", // reported as Inconsistency.rule
      body: [[x, parent, x]],
      inconsistent: [x], // up to five terms
    },
  ],
});
reasoner.addRule(anotherRule); // also fine after run(); recomputes once
```

- Custom rules run in the same semi-naive fixpoint as the OWL 2 RL rules, so
  they see derived triples and `owl:sameAs` classes, and their heads feed the
  OWL rules. A head may derive `owl:sameAs`.
- Derived triples are ordinary triples of the closure. `closure("complete")`
  lists them; `closure("application")` lists them under the same filters as any
  other triple (literal subjects, reflexive `owl:sameAs`, skolems and blank-node
  classes are omitted).
- `extend` stays incremental. `retract` does not: with any custom rule
  registered it recomputes the whole closure (the result still equals a fresh
  run), because a custom rule can relate any triples.
- An invalid rule throws an `Error`: unbound head variable, empty body, no head
  and no `inconsistent`, a literal or blank-node head predicate, a duplicate
  name, or a name that is an OWL 2 RL rule name.

## Testing

- `deno task ci`: format, lint, type-check, unit tests.
- `deno task test:parity`: the closure against the Wiki's current engine
  (`rdfjs-inference-engine`), triple for triple, on the corpora in
  `test/parity/corpora/`. Every difference must be a documented divergence.
- `deno task test:w3c`: the W3C OWL 2 RL test cases (approved and proposed),
  fetched from w3.org into `.cache/`. A test in `test/w3c/expected-pass.json`
  that fails is a regression; `deno task test:w3c:update` records new passes.
- `deno task test:differential [--seeds N]`: `Reasoner.extend` and `retract`
  against a fresh run on random graphs (modes extend, retract, retract-instance,
  retract-full, extend-custom, retract-custom, and, with triples spread over
  four named graphs, union-extend, union-retract, graphs-extend, graphs-retract,
  graphs-retract-partial; the graph modes run on every third seed unless
  `--graph-stride 1`); exits 1 on a new failure class. CI runs 1000 seeds (about
  7 s); a nightly workflow runs 5000.
- `deno task bench`: closure time and memory on synthetic graphs
  (`--sizes 1e3,1e4,1e5 --profile plain|equality`).

## Conformance

- **W3C OWL 2 RL suite** (`deno task test:w3c`): 88 of 90 pass. The harness
  reads tests given in OWL functional syntax (a subset, `functional-syntax.ts`),
  follows `owl:imports`, and ignores annotations in the conclusion of
  Direct-Semantics tests. Two conclusions are not entailed, each with its reason
  in `test/w3c/known-gaps.json`: `WebOnt-I5.26-010` and `WebOnt-I5.5-005` (bare
  anonymous class expressions, which the rules never create).
  `New-Feature-ObjectPropertyChain-BJP-002` passes through a rule outside the RL
  table, `prp-trp-chain`: a transitive property gets a skolem `(p p)` chain
  axiom, which the `"application"` view hides.
- **Datatype value equality (dt-eq), numeric and boolean only.** Literals that
  are the same value are put in one `owl:sameAs` class, so functional-property,
  inverse-functional and `owl:hasKey` merges, `owl:differentFrom` and
  `owl:AllDifferent` see them as one value. The spaces follow OWL 2's datatype
  map: `xsd:decimal` and the whole integer family are one space
  (`"1"^^xsd:integer`, `"01"^^xsd:int` and `"1.0"^^xsd:decimal` agree, and
  `"1.0"^^xsd:decimal` is a value of `xsd:integer`), `xsd:float` and
  `xsd:double` are one space each (never equal to each other or to a decimal;
  `+0` and `-0` stay distinct; `NaN` equals nothing), and `xsd:boolean` values
  `"true"`/`"1"` and `"false"`/`"0"` agree. Literals are grouped by value, so
  the cost is linear in the graph's literals. Behavior changes: a subject now
  also holds every equal spelling a literal of the graph has
  (`ex:a ex:p "1"^^xsd:integer` with `"1.0"^^xsd:decimal` used anywhere gives
  `ex:a ex:p "1.0"^^xsd:decimal`, the eq-rep-o copy, in both the `"complete"`
  and `"application"` views), and `isInstanceOf` for the decimal family tests
  the value space rather than the spelling. Unchanged deviations: strings,
  dateTime, binary, anyURI and other datatypes still have one term per spelling,
  no `owl:differentFrom` is materialized between distinct literals, and `dt-eq`
  is never applied to unrelated literals.
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
  component of deleted triples about individuals (an index of components is kept
  as triples are asserted). Deleting a schema triple, such as a subclass or a
  restriction, or a component past `maxScope` recomputes the whole closure. This
  shares its "what does this change touch" question with the scoped SHACL
  validation planned for Worlds
  ([worlds-sdk-ts#151](https://github.com/wazootech/worlds-sdk-ts/issues/151)).
- **Gated like `sparql-engine`.** Done means the W3C OWL 2 RL conformance tests
  pass in CI, and the closure matches the Wiki's current engine triple for
  triple on its parity corpora before the Wiki switches over.

## Relationship to `sparql-engine`

A separate package that depends on `@wazoo/sparql-engine`'s term model. Querying
and reasoning have different specifications, test suites, and release cadences,
so neither forces a release of the other.
