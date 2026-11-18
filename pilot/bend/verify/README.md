# Bend verification pilot (reasoner#45)

Laws about `rdfs:subClassOf` transitivity (rule `scm-sco`), proved in Bend 2 and
checked twice: by `bend` and by its Lean-proved kernel (`--verdict`).

| File             | What it is                                                              |
| ---------------- | ----------------------------------------------------------------------- |
| `sco.bend`       | The code: edges, membership, `step` (one naive round), `iter`, `subset` |
| `LAWS.bend`      | The claims, written by a human; each is an open `law`                   |
| `PROOF.bend`     | One def per law; `bend PROOF.bend --verdict` is the gate                |
| `logic.bend`     | Lemmas about `Bool`, `Nat` equality and edge equality                   |
| `mem.bend`       | Lemmas about membership and `append`                                    |
| `compose.bend`   | Lemmas that `compose` finds `a -> c` from `a -> b` and `b -> c`         |
| `elim.bend`      | Lemmas that take `compose` membership apart (the soundness half)        |
| `loop.bend`      | Lemmas about the stop test `subset` and about `iter`                    |
| `oracle_test.ts` | Differential test of the compiled model against `reference.ts`          |

## What is proved

Six laws, all for every input:

| Law                 | Says                                                                 |
| ------------------- | -------------------------------------------------------------------- |
| `step_mono`         | One round never loses an edge.                                       |
| `step_closes`       | If `a -> b` and `b -> c` are present, the next round has `a -> c`.   |
| `step_sound`        | Every edge a round has was already there or is a composition of two. |
| `stable_is_closed`  | If a round adds nothing, the graph is transitively closed.           |
| `iter_keeps_input`  | `iter(n, es)` keeps every input edge.                                |
| `stop_means_closed` | If `subset(step(r), r)` passes on `r = iter(n, es)`, `r` is closed.  |

The first three pin `step` down completely: its edges are exactly the input plus
the compositions. The last two say the loop's answer is right whenever its stop
test passes.

## What is not proved

- **Termination.** Nothing says `n` rounds are enough. The caller checks the
  stop test; Bend proves the answer is right when it passes. For an oracle this
  is enough: a test asserts the test passes.
- **Least closure.** That `iter` returns the smallest closed superset (nothing
  extra anywhere along the loop) needs a hypothesis used several times in an
  induction. Bend's functions are affine, so such a hypothesis can be used once;
  only Bool equalities can be duplicated. It is doable but a separate piece of
  work.
- **The other five rules** in `reference.ts`, and semi-naive equals naive.
- **The model keeps duplicates.** A cyclic graph makes its lists grow quickly,
  and `mem` then overflows the JS stack. A dedupe step needs its own proof.

## Run

Needs Bend 2.0.x, and for `--verdict` Lean v4.34.0 on the PATH (elan).

```sh
bend pilot/bend/verify/PROOF.bend --verdict   # ALL PROOFS CHECK
deno test --allow-read --allow-write --allow-run --allow-env \
  pilot/bend/verify/oracle_test.ts            # compiles sco.bend, compares
```

The oracle test skips itself when `bend` is not on the PATH. It is not part of
CI: `pilot/` is outside `deno task test`.

## How far to trust it

A pass means every law holds for every input, not for sampled ones. It is only
as meaningful as the claims, so read `LAWS.bend`. The proofs are written against
the exact shape of `sco.bend`, so any change to the code breaks them: three
mutants (a wrong join test, dropping the input from `step`, a loose `neq`) were
each rejected. That shows the proofs track the code, not that each law is strong
by itself; the strength is the six laws together.
