# Bend verification pilot (reasoner#45)

Laws about the pilot's OWL 2 RL rules, proved in Bend 2 and checked twice: by
`bend` and by its Lean-proved kernel (`--verdict`). The proved model also runs:
it compiles to JS and serves as a differential-test oracle for `reference.ts`.

Two models, in the order they were built:

- **scm-sco** (`sco.bend`, `LAWS.bend`, `PROOF.bend`): one rule,
  `rdfs:subClassOf` transitivity over edges. Small enough to read end to end.
- **six rules** (`rl.bend`, `RL_LAWS.bend`, `RL_PROOF.bend`): every rule in
  `reference.ts`, over triples. The laws below are about this one.

## The six-rule model

`fire(a, b, ts)` is every conclusion of the seven rules whose two premises are
`a` and `b` (cax-sco, scm-sco, prp-dom, prp-rng, prp-inv1, prp-inv2, prp-trp;
the last also looks up `(p type TransitiveProperty)` in `ts`). `step` adds
whatever `fire` derives over every pair and is missing; `iter(n, ts)` is `n`
rounds; `subset(step(r), r)` is the stop test. `iter_semi(n, old, delta)` is the
semi-naive loop: it fires only pairs with a new triple, and `semi_fixed` is its
stop test. Start it with `old = TNil{}` and `delta` the input.

### What is proved (`RL_LAWS.bend`)

18 laws, each for every input:

| Law                              | Says                                                                                   |
| -------------------------------- | -------------------------------------------------------------------------------------- |
| `step_mono`                      | A round never loses a triple.                                                          |
| `cax_sco` ... `prp_trp` (7 laws) | If a rule's premises are present, the next round has its conclusion.                   |
| `step_sound`                     | Whatever a round has was there, or follows from two triples by a rule in the table.    |
| `iter_keeps_input`               | `n` rounds keep every input triple.                                                    |
| `stop_means_closed`              | If the stop test passes, the result is closed under every rule.                        |
| `least_closure`                  | The naive loop stays inside any stable superset of its input: it is the smallest.      |
| `semi_skip_safe`                 | A semi-naive round that skips pairs of old triples loses nothing (see below).          |
| `empty_partner`                  | A join against an empty relation fires nothing.                                        |
| `semi_keeps_input`               | The semi-naive loop keeps every input triple.                                          |
| `semi_stop_closed`               | When `semi_fixed` passes, the semi-naive result is closed under every rule.            |
| `semi_least`                     | The semi-naive loop stays inside any stable superset of its input: it invents nothing. |
| `semi_equals_naive`              | If both stop tests pass, the two loops hold exactly the same triples.                  |

"The rule table" is `Rule` in `rl_spec.bend`, written in fields rather than in
terms of the model's guards, so soundness is checked against an independent
statement of the rules.

### The semi-naive skip law, and a flaw it found

`semi_skip_safe` is the argument behind #40's skips: if every firing among old
triples is already stored, the pairs a semi-naive round skips (both premises
old) lose nothing. Stating it exposed a trap in prp-trp. Its third premise,
`(p type TransitiveProperty)`, is a lookup, so a transitive declaration that is
_new_ can enable a firing between two _old_ data triples, and no pair with a new
triple triggers it. A semi-naive round that only joins pairs with a new triple
misses `(1 p 3)` given old `(1 p 2)`, `(2 p 3)` and a new declaration of `p`.
`derive_semi` therefore also joins every pair when `delta` declares a transitive
property, and the law checks old pairs against the _old_ graph. Without that
seed the law cannot be proved, and the differential test fails.

### How the loop-level laws were proved

A loop invariant ("every firing among old triples is already stored") is a
hypothesis used again at every round, and a pointwise fact has to become the
Bool `subset` the next round needs. Bend's functions are affine, so neither
works directly. Two things make it work (`rl_pw.bend`):

- the hypothesis is a Bool equality, which `dup` copies by one rewrite;
- the per-element proof is a _template_ (`~g`), which may be used many times but
  must be closed, so it takes its context as a data argument (`SemiCx` and its
  siblings in `rl.bend`) instead of capturing a variable.

With those, `subset_pw` turns "every member of `l` is in `T`" into
`subset(l, T)` with one recursive call, and each loop law is an induction on the
round count.

### What is not proved

- **That a given `n` is enough rounds.** Both loops take a round count `n` (that
  is how Bend sees them terminate, structurally) and the caller checks the stop
  test. Every law above is for any `n` for which the stop test passes. A bound
  on how many rounds suffice needs a counting argument (a duplicate-free list of
  triples over a finite id set is finite), which is not attempted.
- **Scale.** The model joins every pair, so it is quadratic per round: about 1 s
  at 100 triples and 45 s at 400 on the `plain` profile (`scale_probe.ts`).
  Semi-naive is not faster there, since the first round joins everything.
  Equality of ids (`neq`) also counts down structurally so proofs can unfold it,
  so id size matters too. A 10^5-triple run needs an indexed join and an O(1)
  equality, which is a different model with a much larger proof.

## Files

| File                                                               | What it is                                                                   |
| ------------------------------------------------------------------ | ---------------------------------------------------------------------------- |
| `rl.bend`                                                          | The model: triples, deduped `step`, `fire`, `pairs`, `derive_semi`, loops    |
| `RL_LAWS.bend`, `RL_PROOF.bend`                                    | The claims, and one def per law                                              |
| `rl_spec.bend`                                                     | The rule table as a type                                                     |
| `rl_rules.bend`, `rl_semi.bend`, `rl_fmono.bend`                   | Per-rule proofs, generated from one pattern for all seven rules              |
| `rl_pairs.bend`, `rl_guard.bend`                                   | `pairs_has` / `pairs_elim`; guarded singletons                               |
| `rl_pw.bend`, `rl_sub.bend`, `rl_fresh.bend`                       | `subset_pw` and `dup`; subset and `fresh_go` lemmas                          |
| `rl_least.bend`                                                    | Least closure for the naive loop                                             |
| `rl_skip.bend`, `rl_sin.bend`, `rl_semiloop.bend`, `rl_final.bend` | The skip law; the semi-naive loop; the two loops agree                       |
| `rl_logic`, `rl_mem`, `rl_dedupe`, `rl_loop`                       | Lemmas for triples, generated from the scm-sco ones by renaming              |
| `sco.bend` and its `LAWS`/`PROOF`                                  | The one-rule model, with `logic`, `mem`, `compose`, `elim`, `dedupe`, `loop` |
| `bend_util.ts`                                                     | Compile-and-load helper, and the `Uint32Array` boundary                      |
| `oracle_test.ts`, `rl_oracle_test.ts`                              | Differential tests of the compiled models                                    |
| `scale_probe.ts`                                                   | Not a test: timings against the reference                                    |

## Run

Needs Bend 2.0.x, and for `--verdict` Lean v4.34.0 on the PATH (elan).

```sh
bend pilot/bend/verify/RL_PROOF.bend --verdict   # ALL PROOFS CHECK (under a minute)
bend pilot/bend/verify/PROOF.bend --verdict      # the one-rule model
deno test --allow-read --allow-write --allow-run --allow-env pilot/bend/
```

The Bend tests skip themselves when `bend` is not on the PATH. None of it is in
CI: `pilot/` is outside `deno task test`.

## How far to trust it

A pass means every law holds for every input, not for sampled ones. It is only
as meaningful as the claims, so read `RL_LAWS.bend` and `rl_spec.bend`.

The proofs are written against the exact shape of the code, so any change to it
breaks them. Mutants of `rl.bend` were each rejected: a wrong rule conclusion, a
dropped lookup premise, a one-sided semi-naive join, a missing transitive seed,
a `step` that forgets the graph, a stop test that always passes, a loop that
forgets the old graph. That shows the proofs track the code, not that each law
is strong alone; the strength is the laws together, and the differential tests
tie the proved model back to `reference.ts`, brute force and `Reasoner`.
